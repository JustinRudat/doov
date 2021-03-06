package io.doov.js.ast.num;

import static io.doov.core.dsl.DOOV.when;
import static io.doov.js.ast.ScriptEngineFactory.fieldModelToJS;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.ByteArrayOutputStream;
import java.nio.charset.Charset;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.junit.jupiter.api.*;

import io.doov.core.dsl.field.types.IntegerFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.runtime.GenericModel;
import io.doov.js.ast.AstJavascriptWriter;
import io.doov.js.ast.ScriptEngineFactory;

public class NumericConditionJavascriptTest {

    private ValidationRule rule;
    private static GenericModel model = new GenericModel();
    private static IntegerFieldInfo A = model.intField(1, "A"),
            B = model.intField(2, "B");
    private String request, result = "";
    private static ByteArrayOutputStream ops;
    private static ScriptEngine engine;
    private static AstJavascriptWriter writer;

    @BeforeAll
    static void init() {
        ops = new ByteArrayOutputStream();
        engine = ScriptEngineFactory.create();
        writer = new AstJavascriptWriter(ops);
    }

    @BeforeEach
    void beforeEach() throws ScriptException {
        ops.reset();
        engine.eval(fieldModelToJS(model));
    }

    @Test
    void eval_lesserThan_value() throws ScriptException {
        rule = when(A.lesserThan(0)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_lesserThan_field() throws ScriptException {
        rule = when(B.lesserThan(A)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_lesserOrEquals_value() throws ScriptException {
        rule = when(A.lesserOrEquals(0)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_lesserOrEquals_field() throws ScriptException {
        rule = when(B.lesserOrEquals(A)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_greaterThan_value() throws ScriptException {
        rule = when(A.greaterThan(2)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_greaterThan_field() throws ScriptException {
        rule = when(A.greaterThan(B)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_greaterOrEquals_value() throws ScriptException {
        rule = when(A.greaterOrEquals(2)).validate();
        writer.writeRule(rule);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_greaterOrEquals_field() throws ScriptException {
        rule = when(A.greaterOrEquals(B)).validate();
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
