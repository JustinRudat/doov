package io.doov.sample.validation.js.ast;

import static io.doov.core.dsl.impl.DefaultRuleRegistry.REGISTRY_DEFAULT;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.Charset;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import io.doov.js.ast.JavascriptWriter;
import io.doov.js.ast.ScriptEngineFactory;
import io.doov.sample.validation.SampleRules;

public class JsVisitorTest {

    private static ScriptEngine engine;

    @BeforeAll
    public static void init() throws ScriptException {
        new SampleRules();
        engine = ScriptEngineFactory.create();
        engine.eval(ScriptEngineFactory.evalTestData());
    }

    @Test
    public void print_javascript_syntax_tree() throws ScriptException {
        ByteArrayOutputStream ops = new ByteArrayOutputStream();
        REGISTRY_DEFAULT.stream()
                .peek(rule -> {
                    try {
                        ops.write("--------------------------------\n".getBytes());
                        System.out.println(new String(ops.toByteArray(), Charset.forName("UTF-8")));
                        ops.reset();
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                })
                .forEach(rule -> {
                    try {
                        new JavascriptWriter(ops).writeRule(rule);
                        System.out.println(new String(ops.toByteArray(), Charset.forName("UTF-8")));
                        System.out.println(engine.eval(ops.toString()).toString());
                        ops.reset();
                    } catch (ScriptException e) {
                        e.printStackTrace();
                    }
                });
    }

}
