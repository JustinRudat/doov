package io.doov.js.ast.time;

import io.doov.core.dsl.field.types.IntegerFieldInfo;
import io.doov.core.dsl.field.types.LocalDateFieldInfo;
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
import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.Locale;

import static io.doov.core.dsl.DOOV.when;
import static io.doov.core.dsl.meta.i18n.ResourceBundleProvider.BUNDLE;
import static io.doov.core.dsl.time.TemporalAdjuster.firstDayOfYear;
import static io.doov.js.ast.ScriptEngineFactory.fieldModelToJS;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class TemporalFunctionJavascriptTest {
    private ValidationRule rule;
    private GenericModel model = new GenericModel();
    private LocalDateFieldInfo A = model.localDateField(LocalDate.now(), "A");
    private IntegerFieldInfo B = model.intField(1, "B");
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
    void eval_with() {
        rule = when(A.with(firstDayOfYear()).eq(LocalDate.of(1,1,1))).validate();
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
    void eval_minus_value() {
        rule = when(A.minus(1, ChronoUnit.DAYS).eq(LocalDate.of(1,1,1))).validate();
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
    void eval_minus_field() {
        rule = when(A.minus(B,ChronoUnit.DAYS).eq(LocalDate.of(1,1,1))).validate();
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
    void eval_plus_value() {
        rule = when(A.plus(1, ChronoUnit.DAYS).eq(LocalDate.of(1,1,1))).validate();
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
    void eval_() {
        rule = when(A.plus(B, ChronoUnit.DAYS).eq(LocalDate.of(1,1,1))).validate();
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
