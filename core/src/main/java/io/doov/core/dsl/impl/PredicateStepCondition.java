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
package io.doov.core.dsl.impl;

import java.util.Optional;
import java.util.function.BiFunction;
import java.util.function.Function;

import io.doov.core.dsl.DslModel;
import io.doov.core.dsl.lang.Context;
import io.doov.core.dsl.meta.Metadata;

class PredicateStepCondition<N> extends AbstractStepCondition {

    PredicateStepCondition(Metadata metadata,
                    BiFunction<DslModel, Context, Optional<N>> value,
                    Function<N, Boolean> predicate) {
        super(metadata, (model, context) -> value.apply(model, context).map(predicate).orElse(false));
    }

    PredicateStepCondition(Metadata metadata,
                    BiFunction<DslModel, Context, Optional<N>> left,
                    BiFunction<DslModel, Context, Optional<N>> right,
                    BiFunction<N, N, Boolean> predicate) {
        super(metadata, (model, context) ->
                        left.apply(model, context)
                                        .flatMap(l -> right.apply(model, context).map(r -> predicate.apply(l, r)))
                                        .orElse(false));
    }

}
