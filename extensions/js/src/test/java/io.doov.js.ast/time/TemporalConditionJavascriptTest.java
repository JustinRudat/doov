package io.doov.js.ast.time;

import io.doov.core.dsl.field.types.LocalDateFieldInfo;
import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.i18n.ResourceBundleProvider;
import io.doov.core.dsl.runtime.GenericModel;
import io.doov.core.dsl.time.LocalDateSuppliers;
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
import java.util.Locale;

import static io.doov.core.dsl.DOOV.when;
import static io.doov.core.dsl.meta.i18n.ResourceBundleProvider.BUNDLE;
import static io.doov.js.ast.ScriptEngineFactory.fieldModelToJS;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class TemporalConditionJavascriptTest {
    private ValidationRule rule;
    private GenericModel model = new GenericModel();
    private LocalDateFieldInfo A = model.localDateField(LocalDate.now(), "A"),
            B = model.localDateField(LocalDate.now().plusDays(1), "B");
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
    void eval_eqCondition() {
        rule = when(A.eq(B)).validate();
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
    void eval_before_value() {
        rule = when(A.before(LocalDate.of(1,1,1))).validate();
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
    void eval_before_field() {
        rule = when(B.before(A)).validate();
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
    void eval_before_condition() {
        rule = when(A.before(LocalDateSuppliers.date(1, 1, 1))).validate();
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
    void eval_beforeOrEq_value() {
        rule = when(A.beforeOrEq(LocalDate.of(1,1,1))).validate();
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
    void eval_beforeOrEq_condition() {
        rule = when(A.beforeOrEq(LocalDateSuppliers.date(1,1,1))).validate();
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
    void eval_after_value() {
        rule = when(A.after(LocalDate.of(2100,1,1))).validate();
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
    void eval_after_field() {
        rule = when(A.after(B)).validate();
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
    void eval_after_condition() {
        rule = when(A.after(LocalDateSuppliers.date(1,1,1))).validate();
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
    void eval_afterOrEq_value() {
        rule = when(A.afterOrEq(LocalDate.of(2100,1,1))).validate();
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
    void eval_afterOrEq_condition() {
        rule = when(A.afterOrEq(LocalDateSuppliers.date(2100,1,1))).validate();
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
