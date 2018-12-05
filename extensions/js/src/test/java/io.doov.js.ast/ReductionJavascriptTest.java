package io.doov.js.ast;

import io.doov.core.FieldModel;
import io.doov.core.dsl.field.types.IntegerFieldInfo;
import io.doov.core.dsl.field.types.LocalDateFieldInfo;
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
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.time.LocalDate;
import java.util.Locale;

import static io.doov.core.dsl.DOOV.when;
import static io.doov.core.dsl.meta.i18n.ResourceBundleProvider.BUNDLE;
import static io.doov.core.dsl.time.LocalDateSuppliers.today;
import static java.time.temporal.ChronoUnit.MONTHS;
import static java.time.temporal.ChronoUnit.YEARS;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class ReductionJavascriptTest {

    private ValidationRule rule;
    private GenericModel model;
    private LocalDateFieldInfo userbd;
    private IntegerFieldInfo configMaxEmailSize;
    private String request;

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
        this.model = new GenericModel();
        this.userbd = model.localDateField(LocalDate.of(1980, 1, 1), "userbd");
        this.configMaxEmailSize = model.intField(3, "maxsize");
        ops.reset();
        String varJS = fieldModelToJS(model);
        engine.eval(varJS);
    }

    @Test
    void reduce_times_chaining() {
        rule = when(configMaxEmailSize.times(2).times(2).times(2)
                .eq(24)).validate().withShortCircuit(false);

        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            assertEquals("true", engine.eval(request).toString());
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }


    // From here, doc stands for date_operator_chaining
    @Test
    void reduce_doc_years_between() {
        rule = when(today().plus(2, YEARS)
                .yearsBetween(today().plus(12, MONTHS).plus(1, YEARS))
                .eq(0)).validate().withShortCircuit(false);
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            assertEquals("true", engine.eval(request).toString());
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void reduce_doc_birthdateEq() {
        rule = when(userbd.plus(2, YEARS)
                .yearsBetween(userbd.plus(12, MONTHS).plus(1, YEARS))
                .eq(0)).validate().withShortCircuit(false);
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            assertEquals("true", engine.eval(request).toString());
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void reduce_doc_todayEq() {
        rule = when(today().plus(2, YEARS).minus(12, MONTHS).minus(1, YEARS)
                .eq(today())).validate().withShortCircuit(false);
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            assertEquals("true", engine.eval(request).toString());
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @Test
    void reduce_doc_value(){
        rule = when(userbd.yearsBetween(today()).eq(38)).validate().withShortCircuit(false);
        visitor.browse(rule.metadata(), 0);
        request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
        try {
            assertEquals("true", engine.eval(request).toString());
        } catch (ScriptException e) {
            e.printStackTrace();
        }
    }

    @AfterEach
    void afterEach() {
        System.out.println("> " + request);
    }

    private String fieldModelToJS(FieldModel model) {
        ByteArrayOutputStream opsTmp = new ByteArrayOutputStream();
        model.getFieldInfos().stream().forEach(fieldName ->
        {
            try {
                if(fieldName.type()==LocalDate.class || fieldName.type() == String.class){
                    opsTmp.write(("var " + fieldName.readable() + " = \'" + model.getAsString(fieldName) + "\' ;\n").getBytes(StandardCharsets.UTF_8));
                }else{
                    opsTmp.write(("var " + fieldName.readable() + " = " + model.getAsString(fieldName) + " ;\n").getBytes(StandardCharsets.UTF_8));

                }
            } catch (IOException e) {
                e.printStackTrace();
            }
        });
        model.stream().forEach(entry -> {

        });
        return new String(opsTmp.toByteArray(), Charset.forName("UTF-8"));
    }
}
