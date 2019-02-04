package io.doov.js.ast;

import static io.doov.core.dsl.DOOV.when;
import static io.doov.core.dsl.meta.i18n.ResourceBundleProvider.BUNDLE;
import static io.doov.js.ast.ScriptEngineFactory.fieldModelToJS;
import static java.util.Arrays.asList;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.ByteArrayOutputStream;
import java.nio.charset.Charset;
import java.util.Locale;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.junit.jupiter.api.*;

import io.doov.core.dsl.field.types.StringFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.i18n.ResourceBundleProvider;
import io.doov.core.dsl.runtime.GenericModel;

public class DefaultConditionJavascriptTest {

    private ValidationRule rule;
    private static GenericModel model = new GenericModel();
    private static StringFieldInfo A = model.stringField("value", "A"),
            B = model.stringField(null, "B"),
            C = model.stringField("value", "C"),
            D = model.stringField("", "D");
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
    void eval_isNull() throws ScriptException {
        rule = when(A.isNull()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_isNotNull() throws ScriptException {
        rule = when(B.isNotNull()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_isEmpty() throws ScriptException {
        rule = when(D.isNull()).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_equalsField() throws ScriptException {
        rule = when(B.eq(A)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_equalsValue() throws ScriptException {
        rule = when(A.eq("test")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_notEqualsValue() throws ScriptException {
        rule = when(A.notEq("value")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_notEqualsField() throws ScriptException {
        rule = when(A.notEq(C)).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_anyMatch_values_false() throws ScriptException {
        rule = when(A.anyMatch("a", "b", "c")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_anyMatch_values_true() throws ScriptException {
        rule = when(A.anyMatch("value", "b", "c")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_allMatch_values_false() throws ScriptException {
        rule = when(A.allMatch("value", "b", "c")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_allMatch_values_true() throws ScriptException {
        rule = when(A.allMatch("value", "value", "value")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_allMatch_collection_false() throws ScriptException {
        rule = when(A.allMatch(asList("value", "b", "c"))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_allMatch_collection_true() throws ScriptException {
        rule = when(A.allMatch(asList("value", "value", "value"))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_noneMatch_values_false() throws ScriptException {
        rule = when(A.noneMatch("value", "b", "c")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_noneMatch_collection_false() throws ScriptException {
        rule = when(A.noneMatch(asList("value", "b", "c"))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_noneMatch_values_true() throws ScriptException {
        rule = when(A.noneMatch("a", "b", "c")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_noneMatch_collection_true() throws ScriptException {
        rule = when(A.noneMatch(asList("a", "b", "c"))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @AfterEach
    void afterEach() {
        System.out.println(request + " -> " + result + "\n");
    }

}
