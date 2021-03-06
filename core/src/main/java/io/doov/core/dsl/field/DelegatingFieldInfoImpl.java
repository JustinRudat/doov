/*
 * Copyright (C) by Courtanet, All Rights Reserved.
 */
package io.doov.core.dsl.field;

import io.doov.core.FieldId;
import io.doov.core.FieldInfo;

public abstract class DelegatingFieldInfoImpl implements DelegatingFieldInfo {

    private FieldInfo fieldInfo;

    public DelegatingFieldInfoImpl(FieldInfo fieldInfo) {
        this.fieldInfo = fieldInfo;
    }

    @Override
    public FieldInfo delegate() {
        return fieldInfo;
    }

    @Override
    public FieldId id() {
        return delegate().id();
    }
}
