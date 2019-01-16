package io.doov.js.ast.num;

import io.doov.core.dsl.field.types.IntegerFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.i18n.ResourceBundleProvider;
import io.doov.core.dsl.runtime.GenericModel;
import io.doov.js.ast.AstJavascriptVisitor;
import io.doov.js.ast.ScriptEngineFactory;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import javax.script.ScriptEngine;
import javax.script.ScriptException;
import java.io.ByteArrayOutputStream;
import java.nio.charset.Charset;
import java.util.Locale;

import static io.doov.core.dsl.DOOV.when;
import static io.doov.core.dsl.meta.i18n.ResourceBundleProvider.BUNDLE;
import static io.doov.js.ast.ScriptEngineFactory.fieldModelToJS;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class NumericConditionJavascriptTest {
    private static Locale LOCALE = Locale.US;
    private ValidationRule rule;
    private static GenericModel model = new GenericModel();
    private IntegerFieldInfo A = model.intField(1, "A"),
            B = model.intField(2, "B");
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
    void eval_lesserThan_value() {
        rule = when(A.lesserThan(0)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            result = engine.eval(request).toString();
            assertEquals("false", result);
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void eval_lesserThan_field() {
        rule = when(B.lesserThan(A)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            result = engine.eval(request).toString();
            assertEquals("false", result);
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void eval_lesserOrEquals_value() {
        rule = when(A.lesserOrEquals(0)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            result = engine.eval(request).toString();
            assertEquals("false", result);
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void eval_lesserOrEquals_field() {
        rule = when(B.lesserOrEquals(A)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            result = engine.eval(request).toString();
            assertEquals("false", result);
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void eval_greaterThan_value() {
        rule = when(A.greaterThan(2)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            result = engine.eval(request).toString();
            assertEquals("false", result);
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void eval_greaterThan_field() {
        rule = when(A.greaterThan(B)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            result = engine.eval(request).toString();
            assertEquals("false", result);
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void eval_greaterOrEquals_value() {
        rule = when(A.greaterOrEquals(2)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            result = engine.eval(request).toString();
            assertEquals("false", result);
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void eval_greaterOrEquals_field() {
        rule = when(A.greaterOrEquals(B)).validate();
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            result = engine.eval(request).toString();
            assertEquals("false", result);
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }


    @AfterEach
    void afterEach() {
        System.out.println(request + " -> " + result);
    }
}
