/*
 * Copyright (c) 2019-present Samsung Electronics Co., Ltd
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301
 *  USA
 */

#include "Escargot.h"
#include "EnumerateObject.h"
#include "runtime/EncodedValue.h"
#include "runtime/ArrayObject.h"
#include "runtime/TypedArrayObject.h"

namespace Escargot {

bool EnumerateObject::checkLastEnumerateKey(ExecutionState& state)
{
    if (UNLIKELY(checkIfModified(state))) {
        update(state);
    }

    if (m_index < m_keys.size()) {
        return false;
    }
    return true;
}

void EnumerateObject::update(ExecutionState& state)
{
    EncodedValueTightVector newKeys;
    executeEnumeration(state, newKeys);

    VectorWithInlineStorage<32, Value, GCUtil::gc_malloc_allocator<Value>> differenceKeys;
    for (size_t i = 0; i < newKeys.size(); i++) {
        const auto& key = newKeys[i];
        // If a property that has not yet been visited during enumeration is deleted, then it will not be visited.
        if (std::find(m_keys.begin(), m_keys.begin() + m_index, key) == m_keys.begin() + m_index && std::find(m_keys.begin() + m_index, m_keys.end(), key) != m_keys.end()) {
            // If new properties are added to the object being enumerated during enumeration,
            // the newly added properties are not guaranteed to be visited in the active enumeration.
            differenceKeys.push_back(key);
        }
    }

    m_index = 0;
    m_keys.clear();
    m_keys.resizeWithUninitializedValues(differenceKeys.size());
    for (size_t i = 0; i < differenceKeys.size(); i++) {
        m_keys[i] = differenceKeys[i];
    }
}

bool EnumerateObject::checkIfModified(ExecutionState& state)
{
    if (m_object->isArrayObject()) {
        ArrayObject* obj = m_object->asArrayObject();
        if (UNLIKELY(obj->arrayLength(state) != m_arrayLength)) {
            return true;
        }
        if (obj->isFastModeArray() && m_index < m_keys.size()) {
            Value currentKey = m_keys[m_index];
            auto idx = currentKey.tryToUseAsIndex(state);
            if (idx < m_arrayLength) {
                if (obj->m_fastModeData[idx].isEmpty()) {
                    return true;
                }
            }
        }
    }
    return false;
}

void* EnumerateObjectWithDestruction::operator new(size_t size)
{
    static MAY_THREAD_LOCAL bool typeInited = false;
    static MAY_THREAD_LOCAL GC_descr descr;
    if (!typeInited) {
        GC_word obj_bitmap[GC_BITMAP_SIZE(EnumerateObjectWithDestruction)] = { 0 };
        GC_set_bit(obj_bitmap, GC_WORD_OFFSET(EnumerateObjectWithDestruction, m_keys));
        GC_set_bit(obj_bitmap, GC_WORD_OFFSET(EnumerateObjectWithDestruction, m_object));
        GC_set_bit(obj_bitmap, GC_WORD_OFFSET(EnumerateObjectWithDestruction, m_hiddenClass));
        descr = GC_make_descriptor(obj_bitmap, GC_WORD_LEN(EnumerateObjectWithDestruction));
        typeInited = true;
    }
    return GC_MALLOC_EXPLICITLY_TYPED(size, descr);
}

void* EnumerateObjectWithIteration::operator new(size_t size)
{
    static MAY_THREAD_LOCAL bool typeInited = false;
    static MAY_THREAD_LOCAL GC_descr descr;
    if (!typeInited) {
        GC_word obj_bitmap[GC_BITMAP_SIZE(EnumerateObjectWithIteration)] = { 0 };
        GC_set_bit(obj_bitmap, GC_WORD_OFFSET(EnumerateObjectWithIteration, m_keys));
        GC_set_bit(obj_bitmap, GC_WORD_OFFSET(EnumerateObjectWithIteration, m_object));
        GC_set_bit(obj_bitmap, GC_WORD_OFFSET(EnumerateObjectWithIteration, m_hiddenClassChain));
        descr = GC_make_descriptor(obj_bitmap, GC_WORD_LEN(EnumerateObjectWithIteration));
        typeInited = true;
    }
    return GC_MALLOC_EXPLICITLY_TYPED(size, descr);
}

void EnumerateObjectWithDestruction::fillRestElement(ExecutionState& state, Object* result)
{
    ASSERT(m_index == 0);

    Value key, value;
    while (m_index < m_keys.size()) {
        if (UNLIKELY(checkIfModified(state))) {
            update(state);
        } else {
            key = m_keys[m_index++];
            // check unmarked key and put rest properties
            if (!key.isEmpty()) {
                value = m_object->getIndexedProperty(state, key).value(state, m_object);
                result->setIndexedProperty(state, key, value);
            }
        }
    }
}

void EnumerateObjectWithDestruction::executeEnumeration(ExecutionState& state, EncodedValueTightVector& keys)
{
    ASSERT(!!m_object);

    if (m_object->isArrayObject()) {
        m_arrayLength = m_object->asArrayObject()->arrayLength(state);
    }

    m_hiddenClass = m_object->structure();

    struct Properties {
        std::multiset<Value::ValueIndex, std::less<Value::ValueIndex>> indexes;
        VectorWithInlineStorage<32, EncodedValue, GCUtil::gc_malloc_allocator<EncodedValue>> strings;
        VectorWithInlineStorage<4, Value, GCUtil::gc_malloc_allocator<Value>> symbols;
    } properties;

    m_object->enumeration(state, [](ExecutionState& state, Object* self, const ObjectPropertyName& name, const ObjectStructurePropertyDescriptor& desc, void* data) -> bool {
        auto properties = (Properties*)data;
        auto value = name.toPlainValue();
        if (desc.isEnumerable()) {
            Value::ValueIndex nameAsIndexValue;
            if (value.isSymbol()) {
                properties->symbols.push_back(value);
            } else if (name.isIndexString() && (nameAsIndexValue = value.toIndex(state)) != Value::InvalidIndexValue) {
                properties->indexes.insert(nameAsIndexValue);
            } else {
                properties->strings.push_back(value);
            }
        }
        return true; }, &properties, false);

    keys.resizeWithUninitializedValues(properties.indexes.size() + properties.strings.size() + properties.symbols.size());

    size_t idx = 0;
    for (auto& v : properties.indexes) {
        keys[idx++] = Value(v).toString(state);
    }
    for (auto& v : properties.strings) {
        keys[idx++] = v;
    }
    for (auto& v : properties.symbols) {
        keys[idx++] = v;
    }
}

bool EnumerateObjectWithDestruction::checkIfModified(ExecutionState& state)
{
    if (UNLIKELY(m_hiddenClass != m_object->structure())) {
        return true;
    }

    return EnumerateObject::checkIfModified(state);
}

void EnumerateObjectWithIteration::executeEnumeration(ExecutionState& state, EncodedValueTightVector& keys)
{
    ASSERT(!!m_object);
    m_hiddenClassChain.clear();

    if (UNLIKELY(m_object->isArrayObject())) {
        m_arrayLength = m_object->asArrayObject()->arrayLength(state);
    } else if (UNLIKELY(m_object->isTypedArrayObject() && m_object->asTypedArrayObject()->buffer()->isDetachedBuffer())) {
        return;
    }

    bool shouldSearchProto = false;
    m_hiddenClassChain.push_back(m_object->structure());

    std::unordered_set<String*, std::hash<String*>, std::equal_to<String*>, GCUtil::gc_malloc_allocator<String*>> keyStringSet;

    Object* proto = m_object->getPrototypeObject(state);
    while (proto) {
        if (!shouldSearchProto) {
            if (proto->hasOwnEnumeration()) {
                proto->enumeration(state, [](ExecutionState& state, Object* self, const ObjectPropertyName& name, const ObjectStructurePropertyDescriptor& desc, void* data) -> bool {
                    if (desc.isEnumerable()) {
                        bool* shouldSearchProto = (bool*)data;
                        *shouldSearchProto = true;
                        return false;
                    }
                    return true; }, &shouldSearchProto);

            } else {
                shouldSearchProto |= proto->structure()->hasEnumerableProperty();
            }
        }
        m_hiddenClassChain.push_back(proto->structure());
        proto = proto->getPrototypeObject(state);

        // v8 throw exception when there is too many things on prototype chain
        if (UNLIKELY(m_hiddenClassChain.size() > 1024 * 128)) {
            ErrorObject::throwBuiltinError(state, ErrorCode::RangeError, "Maximum call stack size exceeded");
        }
    }


    if (shouldSearchProto) {
        // TODO sorting properties
        struct EData {
            std::unordered_set<String*, std::hash<String*>, std::equal_to<String*>, GCUtil::gc_malloc_allocator<String*>>* keyStringSet;
            VectorWithInlineStorage<32, EncodedValue, GCUtil::gc_malloc_allocator<EncodedValue>> keys;
            Object* obj;
        } eData;

        eData.keyStringSet = &keyStringSet;
        eData.obj = m_object;

        Object* target = m_object;
        while (target) {
            target->enumeration(state, [](ExecutionState& state, Object* self, const ObjectPropertyName& name, const ObjectStructurePropertyDescriptor& desc, void* data) -> bool {
                EData* eData = (EData*)data;
                if (desc.isEnumerable()) {
                    String* key = name.toPlainValue().toString(state);
                    auto iter = eData->keyStringSet->find(key);
                    if (iter == eData->keyStringSet->end()) {
                        eData->keyStringSet->insert(key);
                        eData->keys.pushBack(Value(key));
                    }
                } else if (self == eData->obj) {
                    // 12.6.4 The values of [[Enumerable]] attributes are not considered
                    // when determining if a property of a prototype object is shadowed by a previous object on the prototype chain.
                    String* key = name.toPlainValue().toString(state);
                    ASSERT(eData->keyStringSet->find(key) == eData->keyStringSet->end());
                    eData->keyStringSet->insert(key);
                }
                return true; }, &eData);
            target = target->getPrototypeObject(state);
        }

        keys.resizeWithUninitializedValues(eData.keys.size());
        for (size_t i = 0; i < eData.keys.size(); i++) {
            keys[i] = eData.keys[i];
        }

    } else {
        if (m_object->hasOwnEnumeration() || m_object->structure()->hasIndexPropertyName()) {
            struct Properties {
                std::multiset<Value::ValueIndex, std::less<Value::ValueIndex>> indexes;
                VectorWithInlineStorage<32, EncodedValue, GCUtil::gc_malloc_allocator<EncodedValue>> strings;
            } properties;

            m_object->enumeration(state, [](ExecutionState& state, Object* self, const ObjectPropertyName& name, const ObjectStructurePropertyDescriptor& desc, void* data) -> bool {
                auto properties = (Properties*)data;
                auto value = name.toPlainValue();
                if (desc.isEnumerable()) {
                    Value::ValueIndex nameAsIndexValue;
                    if (name.isIndexString() && (nameAsIndexValue = value.toIndex(state)) != Value::InvalidIndexValue) {
                        properties->indexes.insert(nameAsIndexValue);
                    } else {
                        properties->strings.push_back(value);
                    }
                }
                return true; }, &properties);

            keys.resizeWithUninitializedValues(properties.indexes.size() + properties.strings.size());
            size_t idx = 0;
            for (auto& v : properties.indexes) {
                keys[idx++] = Value(v).toString(state);
            }
            for (auto& v : properties.strings) {
                keys[idx++] = v;
            }
        } else {
            m_object->enumeration(state, [](ExecutionState& state, Object* self, const ObjectPropertyName& name, const ObjectStructurePropertyDescriptor& desc, void* data) -> bool {
                EncodedValueTightVector* keys = reinterpret_cast<EncodedValueTightVector*>(data);
                auto value = name.toPlainValue();
                if (desc.isEnumerable()) {
                    ASSERT(!name.isIndexString() || value.toIndex(state) == Value::InvalidIndexValue);
                    keys->pushBack(value);
                }
                return true; }, &keys);
        }
    }
}

bool EnumerateObjectWithIteration::checkIfModified(ExecutionState& state)
{
    Object* obj = m_object;
    for (size_t i = 0; i < m_hiddenClassChain.size(); i++) {
        auto hc = m_hiddenClassChain[i];
        ObjectStructure* structure = obj->structure();
        if (UNLIKELY(hc != structure)) {
            return true;
        }
        Object* val = obj->getPrototypeObject(state);
        if (val) {
            obj = val;
        } else {
            break;
        }
    }

    return EnumerateObject::checkIfModified(state);
}
} // namespace Escargot
;
