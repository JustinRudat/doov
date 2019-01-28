package io.doov.js.ast.time;

import static io.doov.core.dsl.DOOV.when;
import static io.doov.core.dsl.meta.i18n.ResourceBundleProvider.BUNDLE;
import static io.doov.core.dsl.time.TemporalAdjuster.firstDayOfYear;
import static io.doov.js.ast.ScriptEngineFactory.evalMomentJs;
import static io.doov.js.ast.ScriptEngineFactory.fieldModelToJS;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.ByteArrayOutputStream;
import java.nio.charset.Charset;
import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.Locale;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.junit.jupiter.api.*;

import io.doov.core.dsl.field.types.IntegerFieldInfo;
import io.doov.core.dsl.field.types.LocalDateFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.i18n.ResourceBundleProvider;
import io.doov.core.dsl.runtime.GenericModel;
import io.doov.js.ast.*;

public class TemporalFunctionJavascriptTest {

    private ValidationRule rule;
    private static GenericModel model = new GenericModel();
    private static LocalDateFieldInfo A = model.localDateField(LocalDate.now(), "A");
    private static IntegerFieldInfo B = model.intField(1, "B");
    private String request, result = "";
    private static ByteArrayOutputStream ops;
    private static ResourceBundleProvider bundle;
    private static ScriptEngine engine;
    private static AstJavascriptVisitor visitor;
    private static JavascriptWriter writer;

    @BeforeAll
    static void init() {
        ops = new ByteArrayOutputStream();
        bundle = BUNDLE;
        engine = ScriptEngineFactory.create();
        visitor = new AstJavascriptVisitor(ops, bundle, Locale.ENGLISH);
        writer = new JavascriptWriter(ops);
    }

    @BeforeEach
    void beforeEach() throws ScriptException {
        ops.reset();
        evalMomentJs(engine);
        engine.eval(fieldModelToJS(model));
    }

    @Test
    void eval_with() throws ScriptException {
        rule = when(A.with(firstDayOfYear()).eq(LocalDate.of(1, 1, 1))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_minus_value() throws ScriptException {
        rule = when(A.minus(1, ChronoUnit.DAYS).eq(LocalDate.of(1, 1, 1))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_minus_field() throws ScriptException {
        rule = when(A.minus(B, ChronoUnit.DAYS).eq(LocalDate.of(1, 1, 1))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_plus_value() throws ScriptException {
        rule = when(A.plus(1, ChronoUnit.DAYS).eq(LocalDate.of(1, 1, 1))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @Test
    void eval_plus_field() throws ScriptException {
        rule = when(A.plus(B, ChronoUnit.DAYS).eq(LocalDate.of(1, 1, 1))).validate();
        writer.writeRule(rule);
        //visitor.browse(rule.metadata(),0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        result = engine.eval(request).toString();
        assertEquals("false", result);
    }

    @AfterEach
    void afterEach() {
        System.out.println(request + " -> " + result);
    }
}
