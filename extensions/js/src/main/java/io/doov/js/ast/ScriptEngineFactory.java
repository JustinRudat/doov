package io.doov.js.ast;

import io.doov.core.FieldModel;
import io.doov.core.dsl.meta.Element;
import io.doov.core.dsl.runtime.GenericModel;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.time.LocalDate;
import java.util.ArrayList;

import static java.nio.charset.StandardCharsets.UTF_8;

public class ScriptEngineFactory {

    private static final String MOMENT_JS_SRC = "/META-INF/resources/webjars/momentjs/2.10.3/min/moment.min.js";
    private static final String ENGINE_NAME = "nashorn";

    public static ScriptEngine create() {
        ScriptEngineManager sem = new ScriptEngineManager();            // creation of an engine manager
        ScriptEngine engine = sem.getEngineByName(ENGINE_NAME);         // engine creation based on nashorn
        try {
            InputStream stream = ScriptEngineFactory.class.getResourceAsStream(MOMENT_JS_SRC);
            InputStreamReader momentJS = new InputStreamReader(stream);
            engine.eval(momentJS);                                      // evaluating moment.js
        } catch (ScriptException se) {
            se.printStackTrace();
        }
        return engine;
    }

    public static String fieldModelToJS(FieldModel model) {
        ByteArrayOutputStream opsTmp = new ByteArrayOutputStream();
        model.getFieldInfos().stream().forEach(fieldName ->
        {
            try {
                if (fieldName.type() == LocalDate.class || fieldName.type() == String.class) {
                    opsTmp.write(("var " + fieldName.readable() + " = \'" + model.getAsString(fieldName) + "\' ;\n").getBytes(UTF_8));
                }else if(fieldName.type().getName().endsWith("ArrayList")){
                    opsTmp.write(("var " + fieldName.readable() + " = [").getBytes(UTF_8));
                    ArrayList<Element> test = new ArrayList<>(model.get(fieldName.id()));
                    while(test.size()>1){
                        opsTmp.write(("\'"+ test.remove(0) + "\', ").getBytes(UTF_8));
                    }
                    opsTmp.write(("\'"+ test.remove(0) + "\'];").getBytes(UTF_8));
                }

                else{
                    opsTmp.write(("var " + fieldName.readable() + " = " + model.getAsString(fieldName) + " ;\n").getBytes(UTF_8));

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


