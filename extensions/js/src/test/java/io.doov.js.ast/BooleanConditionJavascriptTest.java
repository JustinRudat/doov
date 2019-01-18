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
    private BooleanFieldInfo A = model.booleanField(true, "A"),
            B = model.booleanField(false, "B"),
            C = model.booleanField(false, "C");
    private String request, result = "";
    private static ByteArrayOutputStream ops;
    private static ResourceBundleProvider bundle;
    private static ScriptEngine engine;
    private static AstJavascriptVisitor visitor;

    @BeforeAll
    static void init() {
        ops = new ByteArrayOutputStream();
        bundle = BUNDLE;
        engine = ScriptEngineFactory.create();
        visitor = new AstJavascriptVisitor(ops, bundle, Locale.ENGLISH);
    }

    @BeforeEach
    void beforeEach() throws ScriptException {
        ops.reset();
        engine.eval(fieldModelToJS(model));
    }

    @Test
    void eval_not() throws ScriptException {
        rule = when(A.not()).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_andValue() throws ScriptException {
        rule = when(A.and(false)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_andField() throws ScriptException {
        rule = when(A.and(B)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_orValue() throws ScriptException {
        rule = when(B.or(false)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_orField() throws ScriptException {
        rule = when(B.or(C)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_isTrue() throws ScriptException {
        rule = when(B.isTrue()).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_isFalse() throws ScriptException {
        rule = when(A.isFalse()).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @AfterEach
    void afterEach() {
        System.out.println(request + " -> " + result);
    }
}
