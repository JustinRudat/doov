package io.doov.js.ast;

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

import io.doov.core.dsl.field.types.BooleanFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.i18n.ResourceBundleProvider;
import io.doov.core.dsl.runtime.GenericModel;

public class BooleanConditionJavascriptTest {

    private ValidationRule rule;
    private static GenericModel model = new GenericModel();
    private static BooleanFieldInfo A = model.booleanField(true, "A"),
            B = model.booleanField(false, "B"),
            C = model.booleanField(false, "C");
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
    void eval_not_false() throws ScriptException {
        rule = when(A.not()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_not_true() throws ScriptException {
        rule = when(B.not()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_not_second_false() throws ScriptException {
        rule = when(A.and(true).not()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_andValue() throws ScriptException {
        rule = when(A.and(false)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_XOR_value_true() throws ScriptException {
        rule = when(A.xor(false)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_XOR_field_true() throws ScriptException {
        rule = when(A.xor(B)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_XOR_value_false() throws ScriptException {
        rule = when(A.xor(true)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_XOR_field_false() throws ScriptException {
        rule = when(C.xor(B)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_andField() throws ScriptException {
        rule = when(A.and(B)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_orValue() throws ScriptException {
        rule = when(B.or(false)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_orField() throws ScriptException {
        rule = when(B.or(C)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_isTrue_false() throws ScriptException {
        rule = when(B.isTrue()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_isTrue_true() throws ScriptException {
        rule = when(A.isTrue()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_isFalse_false() throws ScriptException {
        rule = when(A.isFalse()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_isFalse_true() throws ScriptException {
        rule = when(B.isFalse()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @AfterEach
    void afterEach() {
        System.out.println(request + " -> " + result);
    }
}
