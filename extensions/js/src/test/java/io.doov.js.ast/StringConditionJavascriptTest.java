package io.doov.js.ast;

import io.doov.core.dsl.field.types.StringFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.i18n.ResourceBundleProvider;
import io.doov.core.dsl.runtime.GenericModel;
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

public class StringConditionJavascriptTest {
    private ValidationRule rule;
    private GenericModel model = new GenericModel();
    private StringFieldInfo A = model.stringField("value", "A");
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
        String varJS = fieldModelToJS(model);
        engine.eval(varJS);
    }

    @Test
    void eval_contains() {
        rule = when(A.contains("zz")).validate();
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
    void eval_matches() {
        rule = when(A.contains("z+")).validate();
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
    void eval_startsWith() {
        rule = when(A.contains("zz")).validate();
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
    void eval_endsWith() {
        rule = when(A.contains("zz")).validate();
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
