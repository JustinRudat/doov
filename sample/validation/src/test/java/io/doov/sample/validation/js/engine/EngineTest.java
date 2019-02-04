package io.doov.sample.validation.js.engine;

import static io.doov.core.dsl.impl.DefaultRuleRegistry.REGISTRY_DEFAULT;
import static io.doov.js.ast.ScriptEngineFactory.create;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import io.doov.js.ast.AstJavascriptWriter;
import io.doov.js.ast.ScriptEngineFactory;
import io.doov.sample.validation.SampleRules;

public class EngineTest {

    @BeforeAll
    public static void init() {
        new SampleRules();
    }

    @Test
    public void exec_javascript_syntax_tree() {

        String mockValue = ScriptEngineFactory.evalTestData();

        System.out.println("Evaluation of the rules :");
        System.out.println("    Mock value : ");
        System.out.println("    " + mockValue);

        ScriptEngine engine = create();
        try {
            engine.eval(mockValue); // evaluating the mock values for testing purpose
        } catch (ScriptException e) {
            throw new RuntimeException(e);
        }
        ByteArrayOutputStream ops = new ByteArrayOutputStream();
        AstJavascriptWriter writer = new AstJavascriptWriter(ops);
        final int[] index = new int[1];                                 // index as a tab, usage in lambda expression
        final int[] counter = new int[1];
        index[0] = 0;
        counter[0] = 0;
        REGISTRY_DEFAULT.stream().forEach(rule -> {
            ops.reset();
            try {
                index[0]++;
                System.out.println("--------------------------------\n");
                writer.writeRule(rule);
                String request = new String(ops.toByteArray(), Charset.forName("UTF-8"));
                try {
                    if (index[0] != 14) {                                // excluding some rules for now (lambda
                        // expression)
                        Object obj = engine.eval(request);              // evaluating the current rule to test
                        ops.write(("\n Rules n°" + index[0]).getBytes(StandardCharsets.UTF_8));
                        ops.write(("\n    Starting engine checking of : " + rule.readable() + "\n")
                                .getBytes(StandardCharsets.UTF_8));
                        ops.write(("\t\t-" + obj.toString() + "-\n").getBytes(StandardCharsets.UTF_8));
                        if (obj.toString().equals("true")) {
                            counter[0]++;
                        }
                        ops.write(("    Ending engine checking.\n").getBytes(StandardCharsets.UTF_8));
                    } else {
                        ops.write(("    Skipping engine checking because of mapping issue. Rule n°" + index[0] + "\n")
                                .getBytes(StandardCharsets.UTF_8));
                    }
                } catch (final ScriptException se) {
                    throw new RuntimeException(se);
                }
                System.out.println(new String(ops.toByteArray(), Charset.forName("UTF-8")));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        });
        System.out.println("Passing " + counter[0] + " out of " + index[0] + " tests with true value.");
    }
}
