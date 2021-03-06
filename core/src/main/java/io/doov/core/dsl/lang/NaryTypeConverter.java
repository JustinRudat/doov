package io.doov.core.dsl.lang;

import io.doov.core.dsl.DslField;
import io.doov.core.dsl.DslModel;

/**
 * Generic Type converter
 *
 * @param <O> out type
 */
public interface NaryTypeConverter<O> extends DSLBuilder {
    /**
     * Convert the given in fields in the model to the value in type {@link O}
     *
     * @param fieldModel in model
     * @param context context
     * @param ins in fields
     * @return out value
     */
    O convert(DslModel fieldModel, Context context, DslField... ins);
}
