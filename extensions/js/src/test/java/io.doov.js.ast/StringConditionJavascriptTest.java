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

import io.doov.core.dsl.field.types.StringFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.i18n.ResourceBundleProvider;
import io.doov.core.dsl.runtime.GenericModel;

public class StringConditionJavascriptTest {

    private ValidationRule rule;
    private static GenericModel model = new GenericModel();
    private static StringFieldInfo A = model.stringField("value", "A");
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
    void eval_contains_false() throws ScriptException {
        rule = when(A.contains("zz")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_contains_true() throws ScriptException {
        rule = when(A.contains("alu")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_matches_true() throws ScriptException {
        rule = when(A.matches("alu")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_matches_false() throws ScriptException {
        rule = when(A.matches("z+")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_startsWith_false() throws ScriptException {
        rule = when(A.startsWith("zz")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_endsWith_false() throws ScriptException {
        rule = when(A.endsWith("zz")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));

        result = engine.eval(request).toString();
        assertEquals("false", result);

    }

    @Test
    void eval_startsWith_true() throws ScriptException {
        rule = when(A.startsWith("val")).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("true", result);
    }

    @Test
    void eval_endsWith_true() throws ScriptException {
        rule = when(A.endsWith("ue")).validate();
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
