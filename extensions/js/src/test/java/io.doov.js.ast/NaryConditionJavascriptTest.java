/*
 * Copyright (C) by Courtanet, All Rights Reserved.
 */
package io.doov.js.ast;

import static io.doov.core.dsl.DOOV.count;
import static io.doov.core.dsl.DOOV.min;
import static io.doov.core.dsl.DOOV.sum;
import static io.doov.core.dsl.DOOV.when;
import static io.doov.core.dsl.meta.i18n.ResourceBundleProvider.BUNDLE;
import static io.doov.js.ast.ScriptEngineFactory.fieldModelToJS;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.ByteArrayOutputStream;
import java.nio.charset.Charset;
import java.util.Locale;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.junit.jupiter.api.*;

import io.doov.core.dsl.field.types.NumericFieldInfo;
import io.doov.core.dsl.field.types.StringFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.i18n.ResourceBundleProvider;
import io.doov.core.dsl.runtime.GenericModel;

public class NaryConditionJavascriptTest {

    private ValidationRule rule;
    private static GenericModel model = new GenericModel();
    private static StringFieldInfo A = model.stringField("value", "A"),
            B = model.stringField("test", "B");
    private static NumericFieldInfo E = model.intField(10, "E"),
            F = model.intField(20, "F"),
            G = model.intField(30, "G"),
            H = model.intField(40, "H"),
            I = model.intField(10, "I");
    private String request, result = "";
    private static ByteArrayOutputStream ops;
    private static ResourceBundleProvider bundle;
    private static ScriptEngine engine;
    private static AstJavascriptVisitor visitor;
    private static AstJavascriptWriter writer;

    @BeforeAll
    static void init() {
        ops = new ByteArrayOutputStream();
        bundle = BUNDLE;
        engine = ScriptEngineFactory.create();
        visitor = new AstJavascriptVisitor(ops, bundle, Locale.ENGLISH);
        writer = new AstJavascriptWriter(ops);
    }

    @BeforeEach
    void beforeEach() throws ScriptException {
        ops.reset();
        engine.eval(fieldModelToJS(model));
    }

    @Test
    void eval_count_value_sup() throws ScriptException {
        rule = when(count(A.startsWith("val"), B.matches("[a-z]+")).greaterThan(0)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_count_value_eq() throws ScriptException {
        rule = when(count(A.startsWith("val"), B.matches("[a-z]+")).eq(2)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_sum_eq_value_true() throws ScriptException {
        rule = when(sum(E, F, G, H).eq(100)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_sum_eq_value_false() throws ScriptException {
        rule = when(sum(E, F, G, H).eq(10)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_sum_sup_value_false() throws ScriptException {
        rule = when(sum(E, F, G, H).greaterThan(110)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_sum_sup_value_true() throws ScriptException {
        rule = when(sum(E, F, G, H).greaterThan(90)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_min_eq_value_true() throws ScriptException {
        rule = when(min(E, F, G, H).eq(10)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_min_eq_value_false() throws ScriptException {
        rule = when(min(E, F, G, H).eq(20)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_min_sup_value_true() throws ScriptException {
        rule = when(min(E, F, G, H).greaterThan(5)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_min_sup_field_false() throws ScriptException {
        rule = when(min(E, F, G, H).greaterThan(G)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_min_eq_field_true() throws ScriptException {
        rule = when(min(E, F, G, H).eq(I)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_min_eq_field_false() throws ScriptException {
        rule = when(min(E, F, G, H).eq(F)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @AfterEach
    void afterEach() {
        System.out.println(request + " -> " + result + "\n");
    }

}
