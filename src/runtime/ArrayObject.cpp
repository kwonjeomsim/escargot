/*
 * Copyright (c) 2016-present Samsung Electronics Co., Ltd
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
#include "ArrayObject.h"
#include "TypedArrayObject.h"
#include "ErrorObject.h"
#include "Context.h"
#include "VMInstance.h"

namespace Escargot {

ObjectPropertyValue ArrayObject::DummyArrayElement;

ArrayObject::ArrayObject(ExecutionState& state, ForSpreadArray)
    : DerivedObject(state, state.context()->globalObject()->arrayPrototype(), ESCARGOT_OBJECT_BUILTIN_PROPERTY_NUMBER)
    , m_arrayLength(0)
#if defined(ESCARGOT_64) && defined(ESCARGOT_USE_32BIT_IN_64BIT)
    , m_fastModeData()
#else
    , m_fastModeData(nullptr)
#endif
{
    // SpreadArray should be fast mode
    // it does not affect or be affected by indexed property in other prototype objects
    ensureRareData();
}

ArrayObject::ArrayObject(ExecutionState& state)
    : ArrayObject(state, state.context()->globalObject()->arrayPrototype())
{
}

ArrayObject::ArrayObject(ExecutionState& state, Object* proto)
    : DerivedObject(state, proto, ESCARGOT_OBJECT_BUILTIN_PROPERTY_NUMBER)
    , m_arrayLength(0)
#if defined(ESCARGOT_64) && defined(ESCARGOT_USE_32BIT_IN_64BIT)
    , m_fastModeData()
#else
    , m_fastModeData(nullptr)
#endif
{
    if (UNLIKELY(state.context()->vmInstance()->didSomePrototypeObjectDefineIndexedProperty())) {
#if defined(ESCARGOT_64) && defined(ESCARGOT_USE_32BIT_IN_64BIT)
        m_fastModeData.reset(&ArrayObject::DummyArrayElement);
#else
        m_fastModeData = &ArrayObject::DummyArrayElement;
#endif
    }
}

ArrayObject::ArrayObject(ExecutionState& state, const uint64_t& size, bool shouldConsiderHole)
    : ArrayObject(state, state.context()->globalObject()->arrayPrototype(), size, shouldConsiderHole)
{
}

ArrayObject::ArrayObject(ExecutionState& state, Object* proto, const uint64_t& size, bool shouldConsiderHole)
    : ArrayObject(state, proto)
{
    if (UNLIKELY(size > ((1LL << 32LL) - 1LL))) {
        if (UNLIKELY(state.context()->vmInstance()->didSomePrototypeObjectDefineIndexedProperty())) {
            // m_fastModeData has the initial value `DummyArrayElement`
            // this could trigger an error while destructing of m_fastModeData when an exception thrown right after here
#if defined(ESCARGOT_64) && defined(ESCARGOT_USE_32BIT_IN_64BIT)
            m_fastModeData.reset();
#else
            m_fastModeData = nullptr;
#endif
        }
        ErrorObject::throwBuiltinError(state, ErrorCode::RangeError, ErrorObject::Messages::GlobalObject_InvalidArrayLength);
    }

    setArrayLength(state, size, true, shouldConsiderHole);
}

ArrayObject::ArrayObject(ExecutionState& state, const Value* src, const uint64_t& size)
    : ArrayObject(state, state.context()->globalObject()->arrayPrototype(), src, size)
{
}

ArrayObject::ArrayObject(ExecutionState& state, Object* proto, const Value* src, const uint64_t& size)
    : ArrayObject(state, proto, size, false)
{
    // Let array be ! ArrayCreate(0).
    // Let n be 0.
    // For each element e of elements, do
    // Let status be CreateDataProperty(array, ! ToString(n), e).
    // Assert: status is true.
    // Increment n by 1.
    // Return array.

    if (isFastModeArray()) {
        for (size_t n = 0; n < size; n++) {
            setFastModeArrayValueWithoutExpanding(state, n, src[n]);
        }
    } else {
        for (size_t n = 0; n < size; n++) {
            defineOwnProperty(state, ObjectPropertyName(state, n), ObjectPropertyDescriptor(src[n], ObjectPropertyDescriptor::AllPresent));
        }
    }
}

ArrayObject* ArrayObject::createSpreadArray(ExecutionState& state)
{
    // SpreadArray is a Fixed Array which has no __proto__ property
    // Array.Prototype should not affect any SpreadArray operation
    ArrayObject* spreadArray = new ArrayObject(state, __ForSpreadArray__);
    spreadArray->rareData()->m_isSpreadArrayObject = true;
    spreadArray->rareData()->m_prototype = nullptr;

    return spreadArray;
}

ObjectHasPropertyResult ArrayObject::hasProperty(ExecutionState& state, const ObjectPropertyName& P)
{
    ObjectGetResult v = getVirtualValue(state, P);
    if (LIKELY(v.hasValue())) {
        return ObjectHasPropertyResult(v);
    }

    return Object::hasProperty(state, P);
}


ObjectGetResult ArrayObject::getOwnProperty(ExecutionState& state, const ObjectPropertyName& P)
{
    ObjectGetResult v = getVirtualValue(state, P);
    if (LIKELY(v.hasValue())) {
        return v;
    } else {
        return Object::getOwnProperty(state, P);
    }
}

bool ArrayObject::defineOwnProperty(ExecutionState& state, const ObjectPropertyName& P, const ObjectPropertyDescriptor& desc)
{
    if (!P.isUIntType() && P.objectStructurePropertyName() == state.context()->staticStrings().length) {
        // Let newLen be ToUint32(Desc.[[Value]]).
        uint32_t newLen = 0;

        if (desc.isValuePresent()) {
            newLen = desc.value().toUint32(state);
            // If newLen is not equal to ToNumber( Desc.[[Value]]), throw a RangeError exception.
            if (newLen != desc.value().toNumber(state)) {
                ErrorObject::throwBuiltinError(state, ErrorCode::RangeError, ErrorObject::Messages::GlobalObject_InvalidArrayLength);
            }
        }
        if (!isLengthPropertyWritable() && desc.isValuePresent() && m_arrayLength != newLen) {
            return false;
        }

        if (desc.isConfigurablePresent() && desc.isConfigurable()) {
            return false;
        }

        if (desc.isEnumerablePresent() && desc.isEnumerable()) {
            return false;
        }

        if (desc.isAccessorDescriptor()) {
            return false;
        }

        if (!isLengthPropertyWritable() && desc.isWritable()) {
            return false;
        }

        if (desc.isWritablePresent() && !desc.isWritable()) {
            ensureRareData()->m_isArrayObjectLengthWritable = false;
        }

        if (desc.isValuePresent() && m_arrayLength != newLen) {
            return setArrayLength(state, newLen);
        }

        return true;
    }

    uint32_t idx = P.tryToUseAsIndexProperty();
    if (LIKELY(isFastModeArray())) {
        if (LIKELY(idx != Value::InvalidIndexPropertyValue)) {
            uint32_t len = arrayLength(state);
            if (len > idx && !m_fastModeData[idx].isEmpty()) {
                // Non-empty slot of fast-mode array always has {writable:true, enumerable:true, configurable:true}.
                // So, when new desciptor is not present, keep {w:true, e:true, c:true}
                if (UNLIKELY(!(desc.isValuePresentAlone() || desc.isDataWritableEnumerableConfigurable()))) {
                    convertIntoNonFastMode(state);
                    goto NonFastPath;
                }
            } else if (UNLIKELY(!desc.isDataWritableEnumerableConfigurable())) {
                // In case of empty slot property or over-lengthed property,
                // when new desciptor is not present, keep {w:false, e:false, c:false}
                convertIntoNonFastMode(state);
                goto NonFastPath;
            }

            if (!desc.isValuePresent()) {
                convertIntoNonFastMode(state);
                goto NonFastPath;
            }

            if (UNLIKELY(len <= idx)) {
                if (UNLIKELY(!isExtensible(state))) {
                    goto NonFastPath;
                }
                if (UNLIKELY(!setArrayLength(state, idx + 1)) || UNLIKELY(!isFastModeArray())) {
                    goto NonFastPath;
                }
            }
            m_fastModeData[idx] = desc.value();
            return true;
        }
    }

NonFastPath:

    uint32_t oldLen = arrayLength(state);

    if (idx != Value::InvalidIndexPropertyValue) {
        if ((idx >= oldLen) && !isLengthPropertyWritable())
            return false;
        bool succeeded = DerivedObject::defineOwnProperty(state, P, desc);
        if (!succeeded)
            return false;
        if (idx >= oldLen) {
            return setArrayLength(state, idx + 1);
        }
        return true;
    }

    return DerivedObject::defineOwnProperty(state, P, desc);
}

bool ArrayObject::deleteOwnProperty(ExecutionState& state, const ObjectPropertyName& P)
{
    if (!P.isUIntType() && P.toObjectStructurePropertyName(state) == state.context()->staticStrings().length) {
        return false;
    }

    if (LIKELY(isFastModeArray())) {
        uint32_t idx = P.tryToUseAsIndexProperty();
        if (LIKELY(idx != Value::InvalidIndexPropertyValue)) {
            uint32_t len = arrayLength(state);
            if (idx < len) {
                if (!m_fastModeData[idx].isEmpty()) {
                    m_fastModeData[idx] = Value(Value::EmptyValue);
                }
                return true;
            }
        }
    }

    return Object::deleteOwnProperty(state, P);
}

void ArrayObject::enumeration(ExecutionState& state, bool (*callback)(ExecutionState& state, Object* self, const ObjectPropertyName&, const ObjectStructurePropertyDescriptor& desc, void* data), void* data, bool shouldSkipSymbolKey)
{
    if (LIKELY(isFastModeArray())) {
        size_t len = arrayLength(state);
        for (size_t i = 0; i < len; i++) {
            ASSERT(isFastModeArray());
            if (m_fastModeData[i].isEmpty())
                continue;
            if (!callback(state, this, ObjectPropertyName(state, Value(i)), ObjectStructurePropertyDescriptor::createDataDescriptor(ObjectStructurePropertyDescriptor::AllPresent), data)) {
                return;
            }
        }
    }

    int attr = isLengthPropertyWritable() ? (int)ObjectStructurePropertyDescriptor::WritablePresent : 0;
    if (!callback(state, this, ObjectPropertyName(state.context()->staticStrings().length), ObjectStructurePropertyDescriptor::createDataDescriptor((ObjectStructurePropertyDescriptor::PresentAttribute)attr), data)) {
        return;
    }

    Object::enumeration(state, callback, data, shouldSkipSymbolKey);
}

void ArrayObject::sort(ExecutionState& state, uint64_t length, const std::function<bool(const Value& a, const Value& b)>& comp)
{
    if (length) {
        if (isFastModeArray()) {
            size_t byteLength = sizeof(Value) * length;
            bool canUseStack = byteLength <= 1024;
            Value* tempBuffer = canUseStack ? (Value*)alloca(byteLength) : CustomAllocator<Value>().allocate(length);

            for (uint64_t i = 0; i < length; i++) {
                tempBuffer[i] = m_fastModeData[i];
            }

            Value* tempSpace = canUseStack ? (Value*)alloca(byteLength) : CustomAllocator<Value>().allocate(length);

            mergeSort(tempBuffer, length, tempSpace, [&](const Value& a, const Value& b, bool* lessOrEqualp) -> bool {
                *lessOrEqualp = comp(a, b);
                return true;
            });

            if (UNLIKELY(arrayLength(state) != length)) {
                // array length could be changed due to the compare function executed in the previous merge sort
                setArrayLength(state, length);
            }

            if (LIKELY(isFastModeArray())) {
                for (uint64_t i = 0; i < length; i++) {
                    m_fastModeData[i] = tempBuffer[i];
                }
            } else {
                // fast-mode could be changed due to the compare function executed in the previous merge sort
                for (uint64_t i = 0; i < length; i++) {
                    setIndexedPropertyThrowsException(state, Value(i), tempBuffer[i]);
                }
            }

            if (!canUseStack) {
                GC_FREE(tempSpace);
                GC_FREE(tempBuffer);
            }
        } else {
            Object::sort(state, length, comp);
        }
    }
}

void ArrayObject::toSorted(ExecutionState& state, Object* target, uint64_t length, const std::function<bool(const Value& a, const Value& b)>& comp)
{
    ASSERT(target && target->isArrayObject() && target->length(state) == length);
    ArrayObject* arr = target->asArrayObject();

    if (length) {
        if (isFastModeArray()) {
            size_t byteLength = sizeof(Value) * length;
            bool canUseStack = byteLength <= 1024;
            Value* tempBuffer = canUseStack ? (Value*)alloca(byteLength) : CustomAllocator<Value>().allocate(length);

            for (uint64_t i = 0; i < length; i++) {
                // toSorted handles all hole elements as undefined values
                Value v = m_fastModeData[i];
                tempBuffer[i] = v.isEmpty() ? Value() : v;
            }

            Value* tempSpace = canUseStack ? (Value*)alloca(byteLength) : CustomAllocator<Value>().allocate(length);

            mergeSort(tempBuffer, length, tempSpace, [&](const Value& a, const Value& b, bool* lessOrEqualp) -> bool {
                *lessOrEqualp = comp(a, b);
                return true;
            });

            ASSERT(arr->arrayLength(state) == length);
            if (LIKELY(arr->isFastModeArray())) {
                for (uint64_t i = 0; i < length; i++) {
                    arr->m_fastModeData[i] = tempBuffer[i];
                }
            } else {
                // fast-mode could be changed due to the compare function executed in the previous merge sort
                for (uint64_t i = 0; i < length; i++) {
                    arr->setIndexedProperty(state, Value(i), tempBuffer[i], arr);
                }
            }

            if (!canUseStack) {
                GC_FREE(tempSpace);
                GC_FREE(tempBuffer);
            }
        } else {
            Object::toSorted(state, arr, length, comp);
        }
    }
}

void* ArrayObject::operator new(size_t size)
{
    return CustomAllocator<ArrayObject>().allocate(1);
}

void ArrayObject::iterateArrays(ExecutionState& state, HeapObjectIteratorCallback callback)
{
    iterateSpecificKindOfObject(state, HeapObjectKind::ArrayObjectKind, callback);
}

void ArrayObject::convertIntoNonFastMode(ExecutionState& state)
{
    if (!isFastModeArray())
        return;

    m_structure = structure()->convertToNonTransitionStructure();

    // convert to non-fast mode first because it could affect Object::defineOwnProperty
    // hold a temporal array until the end of non-fast mode conversion
#if defined(ESCARGOT_64) && defined(ESCARGOT_USE_32BIT_IN_64BIT)
    TightVectorWithNoSize<ObjectPropertyValue, CustomAllocator<ObjectPropertyValue>> tempFastModeData(std::move(m_fastModeData));
    m_fastModeData.reset(&ArrayObject::DummyArrayElement);
#else
    ObjectPropertyValue* tempFastModeData = m_fastModeData;
    m_fastModeData = &ArrayObject::DummyArrayElement;
#endif

    auto length = arrayLength(state);
    for (size_t i = 0; i < length; i++) {
        if (!tempFastModeData[i].isEmpty()) {
            Object::defineOwnPropertyThrowsException(state, ObjectPropertyName(state, Value(i)), ObjectPropertyDescriptor(tempFastModeData[i], ObjectPropertyDescriptor::AllPresent));
        }
    }

    // deallocate fast mode data
#if defined(ESCARGOT_64) && defined(ESCARGOT_USE_32BIT_IN_64BIT)
    tempFastModeData.resizeWithUninitializedValues(length, 0);
#else
    GC_FREE(tempFastModeData);
#endif
}

bool ArrayObject::setArrayLength(ExecutionState& state, const Value& newLength)
{
    bool isPrimitiveValue;
    if (LIKELY(newLength.isPrimitive())) {
        isPrimitiveValue = true;
    } else {
        isPrimitiveValue = false;
    }
    // Let newLen be ToUint32(Desc.[[Value]]).
    uint32_t newLen = newLength.toUint32(state);
    // If newLen is not equal to ToNumber( Desc.[[Value]]), throw a RangeError exception.
    if (newLen != newLength.toNumber(state)) {
        ErrorObject::throwBuiltinError(state, ErrorCode::RangeError, ErrorObject::Messages::GlobalObject_InvalidArrayLength);
    }

    bool ret;
    if (UNLIKELY(!isPrimitiveValue && !isLengthPropertyWritable())) {
        ret = false;
    } else {
        ret = setArrayLength(state, newLen, true);
    }
    return ret;
}

bool ArrayObject::setArrayLength(ExecutionState& state, const uint32_t newLength, bool useFitStorage, bool considerHole)
{
    bool isFastMode = isFastModeArray();
    if (UNLIKELY(isFastMode && (newLength > ESCARGOT_ARRAY_NON_FASTMODE_MIN_SIZE) && considerHole)) {
        uint32_t orgLength = arrayLength(state);
        constexpr uint32_t maxSize = std::numeric_limits<uint32_t>::max() / 2;
        if (newLength > orgLength && ((newLength - orgLength > ESCARGOT_ARRAY_NON_FASTMODE_START_MIN_GAP) || newLength >= maxSize)) {
            convertIntoNonFastMode(state);
            isFastMode = false;
        }
    }

    if (LIKELY(isFastMode)) {
        auto oldLength = arrayLength(state);
        if (LIKELY(oldLength != newLength)) {
            m_arrayLength = newLength;
            if (useFitStorage || oldLength == 0 || newLength <= 128) {
                bool hasRD = hasRareData();
#if defined(ESCARGOT_64) && defined(ESCARGOT_USE_32BIT_IN_64BIT)
                m_fastModeData.resizeWithUninitializedValues(oldLength, newLength);

                if (oldLength < newLength) {
                    memset(static_cast<void*>(m_fastModeData.data() + oldLength), 0, sizeof(ObjectPropertyValue) * (newLength - oldLength));
                }
#else
                size_t oldCapacity = hasRD ? (size_t)rareData()->m_arrayObjectFastModeBufferCapacity : 0;
                if (oldCapacity) {
                    if (newLength > oldCapacity) {
                        m_fastModeData = (EncodedValue*)GC_REALLOC(m_fastModeData, sizeof(EncodedValue) * newLength);

                        if (oldLength < newLength) {
                            memset(static_cast<void*>(m_fastModeData + oldLength), 0, sizeof(ObjectPropertyValue) * (newLength - oldLength));
                        }

                    } else {
                        m_fastModeData = (EncodedValue*)GC_REALLOC(m_fastModeData, sizeof(EncodedValue) * newLength);
                    }
                } else {
                    m_fastModeData = (EncodedValue*)GC_REALLOC(m_fastModeData, sizeof(EncodedValue) * newLength);

                    if (oldLength < newLength) {
                        memset(static_cast<void*>(m_fastModeData + oldLength), 0, sizeof(ObjectPropertyValue) * (newLength - oldLength));
                    }
                }
#endif
                if (hasRD) {
                    rareData()->m_arrayObjectFastModeBufferCapacity = 0;
                }
            } else {
                ASSERT(newLength > 128);

                const size_t minExpandCountForUsingLog2Function = 3;
                bool hasRD = hasRareData();
                size_t oldCapacity = hasRD ? (size_t)rareData()->m_arrayObjectFastModeBufferCapacity : oldLength;

#if defined(ESCARGOT_64) && defined(ESCARGOT_USE_32BIT_IN_64BIT)
                auto rd = ensureRareData();
                if (newLength > oldCapacity) {
                    size_t newCapacity;
                    if (rd->m_arrayObjectFastModeBufferExpandCount >= minExpandCountForUsingLog2Function) {
                        ComputeReservedCapacityFunctionWithLog2<> f;
                        newCapacity = f(newLength);
                    } else {
                        ComputeReservedCapacityFunctionWithPercent<130> f;
                        newCapacity = f(newLength);
                    }
                    m_fastModeData.resizeWithUninitializedValues(oldLength, newCapacity);


                    if (oldLength < newLength) {
                        memset(static_cast<void*>(m_fastModeData.data() + oldLength), 0, sizeof(ObjectPropertyValue) * (newLength - oldLength));
                    }

                    rd->m_arrayObjectFastModeBufferCapacity = newCapacity;
                    if (rd->m_arrayObjectFastModeBufferExpandCount < minExpandCountForUsingLog2Function) {
                        rd->m_arrayObjectFastModeBufferExpandCount++;
                    }
                } else {
                    if (oldLength < newLength) {
                        memset(static_cast<void*>(m_fastModeData.data() + oldLength), 0, sizeof(ObjectPropertyValue) * (newLength - oldLength));
                    }

                    rd->m_arrayObjectFastModeBufferCapacity = oldCapacity;
                }
#else
                auto rd = ensureRareData();
                if (newLength > oldCapacity) {
                    size_t newCapacity;
                    if (rd->m_arrayObjectFastModeBufferExpandCount >= minExpandCountForUsingLog2Function) {
                        ComputeReservedCapacityFunctionWithLog2<> f;
                        newCapacity = f(newLength);
                    } else {
                        ComputeReservedCapacityFunctionWithPercent<130> f;
                        newCapacity = f(newLength);
                    }
                    auto newFastModeData = (EncodedValue*)GC_MALLOC(sizeof(EncodedValue) * newCapacity);
                    memcpy(newFastModeData, m_fastModeData, sizeof(EncodedValue) * oldLength);
                    GC_FREE(m_fastModeData);
                    m_fastModeData = newFastModeData;

                    if (oldLength < newLength) {
                        memset(static_cast<void*>(m_fastModeData + oldLength), 0, sizeof(ObjectPropertyValue) * (newLength - oldLength));
                    }

                    rd->m_arrayObjectFastModeBufferCapacity = newCapacity;
                    if (rd->m_arrayObjectFastModeBufferExpandCount < minExpandCountForUsingLog2Function) {
                        rd->m_arrayObjectFastModeBufferExpandCount++;
                    }
                } else {
                    if (oldLength < newLength) {
                        memset(static_cast<void*>(m_fastModeData + oldLength), 0, sizeof(ObjectPropertyValue) * (newLength - oldLength));
                    }
                    rd->m_arrayObjectFastModeBufferCapacity = oldCapacity;
                }
#endif
            }

            if (UNLIKELY(!isLengthPropertyWritable())) {
                convertIntoNonFastMode(state);
            }
        }
        return true;
    } else {
        int64_t oldLen = arrayLength(state);
        int64_t newLen = newLength;

        while (newLen < oldLen) {
            oldLen--;
            ObjectPropertyName key(state, oldLen);

            if (!getOwnProperty(state, key).hasValue()) {
                int64_t result;
                Object::nextIndexBackward(state, this, oldLen, -1, result);
                oldLen = result;

                if (oldLen < newLen) {
                    break;
                }

                key = ObjectPropertyName(state, Value(oldLen));
            }

            bool deleteSucceeded = deleteOwnProperty(state, key);
            if (!deleteSucceeded) {
                m_arrayLength = oldLen + 1;
                return false;
            }
        }
        m_arrayLength = newLength;
        return true;
    }
}

ObjectGetResult ArrayObject::getVirtualValue(ExecutionState& state, const ObjectPropertyName& P)
{
    if (!P.isUIntType() && P.objectStructurePropertyName() == state.context()->staticStrings().length) {
        return ObjectGetResult(Value(m_arrayLength), isLengthPropertyWritable(), false, false);
    }
    if (LIKELY(isFastModeArray())) {
        uint32_t idx = P.tryToUseAsIndexProperty();
        if (LIKELY(idx != Value::InvalidIndexPropertyValue) && LIKELY(idx < arrayLength(state))) {
            Value v = m_fastModeData[idx];
            if (LIKELY(!v.isEmpty())) {
                return ObjectGetResult(v, true, true, true);
            }
            return ObjectGetResult();
        }
    }
    return ObjectGetResult();
}

ObjectHasPropertyResult ArrayObject::hasIndexedProperty(ExecutionState& state, const Value& propertyName)
{
    if (LIKELY(isFastModeArray())) {
        uint32_t idx = propertyName.tryToUseAsIndexProperty(state);
        if (LIKELY(idx != Value::InvalidIndexPropertyValue) && LIKELY(idx < arrayLength(state))) {
            Value v = m_fastModeData[idx];
            if (LIKELY(!v.isEmpty())) {
                return ObjectHasPropertyResult(ObjectGetResult(v, true, true, true));
            }
        }
    }
    return hasProperty(state, ObjectPropertyName(state, propertyName));
}

ObjectGetResult ArrayObject::getIndexedProperty(ExecutionState& state, const Value& property, const Value& receiver)
{
    if (LIKELY(isFastModeArray())) {
        uint32_t idx = property.tryToUseAsIndexProperty(state);
        if (LIKELY(idx != Value::InvalidIndexPropertyValue) && LIKELY(idx < arrayLength(state))) {
            Value v = m_fastModeData[idx];
            if (LIKELY(!v.isEmpty())) {
                return ObjectGetResult(v, true, true, true);
            }
        }
    }
    return get(state, ObjectPropertyName(state, property), receiver);
}

bool ArrayObject::setIndexedProperty(ExecutionState& state, const Value& property, const Value& value, const Value& receiver)
{
    // checking isUint32 to prevent invoke toString on property more than once while calling setIndexedProperty
    if (LIKELY(isFastModeArray() && property.isUInt32())) {
        uint32_t idx = property.tryToUseAsIndexProperty(state);
        if (LIKELY(idx != Value::InvalidIndexPropertyValue)) {
            uint32_t len = arrayLength(state);
            if (UNLIKELY(len <= idx)) {
                if (UNLIKELY(!isExtensible(state))) {
                    return false;
                }
                if (UNLIKELY(!setArrayLength(state, idx + 1)) || UNLIKELY(!isFastModeArray())) {
                    return set(state, ObjectPropertyName(state, property), value, this);
                }
                // fast, non-fast mode can be changed while changing length
                if (LIKELY(isFastModeArray())) {
                    m_fastModeData[idx] = value;
                    return true;
                }
            } else {
                m_fastModeData[idx] = value;
                return true;
            }
        }
    }
    return set(state, ObjectPropertyName(state, property), value, receiver);
}

bool ArrayObject::preventExtensions(ExecutionState& state)
{
    // first, convert to non-fast-mode.
    // then, set preventExtensions
    convertIntoNonFastMode(state);
    return Object::preventExtensions(state);
}

uint64_t ArrayObject::length(ExecutionState& state)
{
    return arrayLength(state);
}

void ArrayObject::markAsPrototypeObject(ExecutionState& state)
{
    Object::markAsPrototypeObject(state);
    convertIntoNonFastMode(state);
}

ArrayIteratorObject::ArrayIteratorObject(ExecutionState& state, Object* a, Type type)
    : IteratorObject(state, state.context()->globalObject()->arrayIteratorPrototype())
    , m_array(a)
    , m_iteratorNextIndex(0)
    , m_type(type)
{
}

void* ArrayIteratorObject::operator new(size_t size)
{
    static MAY_THREAD_LOCAL bool typeInited = false;
    static MAY_THREAD_LOCAL GC_descr descr;
    if (!typeInited) {
        GC_word obj_bitmap[GC_BITMAP_SIZE(ArrayIteratorObject)] = { 0 };
        Object::fillGCDescriptor(obj_bitmap);
        GC_set_bit(obj_bitmap, GC_WORD_OFFSET(ArrayIteratorObject, m_array));
        descr = GC_make_descriptor(obj_bitmap, GC_WORD_LEN(ArrayIteratorObject));
        typeInited = true;
    }
    return GC_MALLOC_EXPLICITLY_TYPED(size, descr);
}

std::pair<Value, bool> ArrayIteratorObject::advance(ExecutionState& state)
{
    // Let a be the value of the [[IteratedObject]] internal slot of O.
    Object* a = m_array;
    // If a is undefined, return CreateIterResultObject(undefined, true).
    if (a == nullptr) {
        return std::make_pair(Value(), true);
    }
    // Let index be the value of the [[ArrayIteratorNextIndex]] internal slot of O.
    size_t index = m_iteratorNextIndex;
    // Let itemKind be the value of the [[ArrayIterationKind]] internal slot of O.
    Type itemKind = m_type;

    size_t len;
    // If a has a [[TypedArrayName]] internal slot, then
    if (a->isTypedArrayObject()) {
        // If IsDetachedBuffer(a.[[ViewedArrayBuffer]]) is true, throw a TypeError exception.
        if (a->asArrayBufferView()->buffer()->isDetachedBuffer()) {
            ErrorObject::throwBuiltinError(state, ErrorCode::TypeError, state.context()->staticStrings().ArrayIterator.string(), true, state.context()->staticStrings().next.string(), ErrorObject::Messages::GlobalObject_DetachedBuffer);
            return std::make_pair(Value(), false);
        }
        // https://tc39.es/ecma262/#sec-istypedarrayoutofbounds
        // 5. Let byteOffsetStart be O.[[ByteOffset]].
        // 6. If O.[[ArrayLength]] is auto, then
        //     a. Let byteOffsetEnd be bufferByteLength.
        // 7. Else,
        //     a. Let elementSize be TypedArrayElementSize(O).
        //     b. Let byteOffsetEnd be byteOffsetStart + O.[[ArrayLength]] × elementSize.
        // 8. If byteOffsetStart > bufferByteLength or byteOffsetEnd > bufferByteLength, return true.
        auto bufferByteLength = a->asArrayBufferView()->buffer()->byteLength();
        auto byteOffsetStart = a->asTypedArrayObject()->byteOffset();
        auto byteOffsetEnd = byteOffsetStart + a->asTypedArrayObject()->byteLength();
        if (byteOffsetStart > bufferByteLength || byteOffsetEnd > bufferByteLength || a->asTypedArrayObject()->wasResetByInvalidByteLength()) {
            ErrorObject::throwBuiltinError(state, ErrorCode::TypeError, state.context()->staticStrings().ArrayIterator.string(), true, state.context()->staticStrings().next.string(), ErrorObject::Messages::GlobalObject_DetachedBuffer);
            return std::make_pair(Value(), false);
        }
        // Let len be a.[[ArrayLength]].
        len = a->asArrayBufferView()->arrayLength();
    } else {
        // Let len be ? ToLength(? Get(a, "length")).
        len = a->length(state);
    }

    // If index ≥ len, then
    if (index >= len) {
        // Set the value of the [[IteratedObject]] internal slot of O to undefined.
        m_array = nullptr;
        // Return CreateIterResultObject(undefined, true).
        return std::make_pair(Value(), true);
    }

    // Set the value of the [[ArrayIteratorNextIndex]] internal slot of O to index+1.
    m_iteratorNextIndex = index + 1;

    // If itemKind is "key", return CreateIterResultObject(index, false).
    if (itemKind == Type::TypeKey) {
        return std::make_pair(Value(index), false);
    } else {
        Value elementValue = a->getIndexedProperty(state, Value(index)).value(state, a);
        if (itemKind == Type::TypeValue) {
            return std::make_pair(elementValue, false);
        } else {
            ASSERT(itemKind == Type::TypeKeyValue);
            Value v[2] = { Value(index), elementValue };
            Value resultValue = Object::createArrayFromList(state, 2, v);
            return std::make_pair(resultValue, false);
        }
    }
}

ArrayPrototypeObject::ArrayPrototypeObject(ExecutionState& state)
    : ArrayObject(state, state.context()->globalObject()->objectPrototype())
{
    convertIntoNonFastMode(state);
}

void ArrayPrototypeObject::markAsPrototypeObject(ExecutionState& state)
{
    if (UNLIKELY(!state.context()->vmInstance()->didSomePrototypeObjectDefineIndexedProperty() && (structure()->hasIndexPropertyName() || isProxyObject()))) {
        state.context()->vmInstance()->somePrototypeObjectDefineIndexedProperty(state);
    }
}

bool ArrayPrototypeObject::isEverSetAsPrototypeObject() const
{
    ASSERT(!hasRareData() || !rareData()->m_isEverSetAsPrototypeObject);
    return true;
}
} // namespace Escargot
