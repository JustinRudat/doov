/*
 * Copyright 2017 Courtanet
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */
package io.doov.core.dsl.field;

import io.doov.core.FieldId;
import io.doov.core.FieldInfo;
import io.doov.core.dsl.impl.TypeCondition;

public class DefaultFieldInfo<T> implements FieldInfo, BaseFieldInfo<T> {

    private final FieldId fieldId;
    private final String readable;
    private final Class<?> type;
    private final Class<?>[] genericTypes;
    private final FieldId[] siblings;

    public DefaultFieldInfo(FieldId fieldId, String readable, Class<?> type, Class<?>[] genericTypes,
                    FieldId... siblings) {
        this.fieldId = fieldId;
        this.readable = readable;
        this.type = type;
        this.genericTypes = genericTypes;
        this.siblings = siblings;
    }

    @Override
    public FieldId id() {
        return fieldId;
    }

    @Override
    public String readable() {
        return readable;
    }

    @Override
    public Class<?> type() {
        return type;
    }

    @Override
    public FieldId[] siblings() {
        return siblings;
    }

    @Override
    public Class<?>[] genericTypes() {
        return genericTypes;
    }

    @Override
    public TypeCondition<T> getTypeCondition() {
        return new TypeCondition<>(this);
    }

}
