/*
 * Copyright 2017 Courtanet
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package io.doov.core.dsl;

import io.doov.core.FieldId;

/**
 * Interface for all model.
 */
public interface DslModel {

    <T> T get(FieldId id);

    default <T> T get(DslField<T> field) {
        return get(field.id());
    }

    <T> void set(FieldId fieldId, T value);

    default <T> void set(DslField<T> field, T value) {
        set(field.id(), value);
    }

}
