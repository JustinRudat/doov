package io.doov.sample.validation.js.ast;

import static io.doov.core.dsl.impl.DefaultRuleRegistry.REGISTRY_DEFAULT;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.Charset;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import io.doov.js.ast.AstJavascriptWriter;
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
    public void print_javascript_syntax_tree() {
        ByteArrayOutputStream ops = new ByteArrayOutputStream();
        AstJavascriptWriter writer = new AstJavascriptWriter(ops);
        REGISTRY_DEFAULT.stream()
                .peek(rule -> {
                    try {
                        ops.write("--------------------------------".getBytes());
                        System.out.println(new String(ops.toByteArray(), Charset.forName("UTF-8")));
                        ops.reset();
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                })
                .forEach(rule -> {
                    writer.writeRule(rule);
                    System.out.println(new String(ops.toByteArray(), Charset.forName("UTF-8")));
                    ops.reset();

                });
    }

}
