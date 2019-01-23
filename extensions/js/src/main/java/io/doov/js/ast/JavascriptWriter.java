/*
 * Copyright (C) by Courtanet, All Rights Reserved.
 */
package io.doov.js.ast;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.stream.Stream;

import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.*;

public class JavascriptWriter {

    protected final OutputStream ops;

    public JavascriptWriter(OutputStream ops) {
        this.ops = ops;
    }

    public void writeRule(ValidationRule rule) {
        writeWhen(rule.metadata());
    }

    public void writeWhen(Metadata whenMetadata) {
        write("if(");
        writeMetadata(whenMetadata.flatten());
        write(") { return true; } else { return false; }");
    }

    public void writeMetadata(List<Element> metadata) {
        metadata.stream().forEach(element -> {
            switch(element.getType()){
                case FIELD:
                    writeField(element);
                    break;
                case OPERATOR:
                    writeOperator((DefaultOperator) element.getReadable());
                    break;
                case VALUE:
                    writeValue(element);
                    break;
                case STRING_VALUE:
                    break;
                case PARENTHESIS_LEFT:
                    break;
                case PARENTHESIS_RIGHT:
                    break;
                case TEMPORAL_UNIT:
                    break;
                case UNKNOWN:
                    break;
            }

        });
    }

    public void writeValue(Element element){

    }

    public void writeField(Element element){

    }

    public void writeOperator(DefaultOperator element){
        switch(element){
            case rule:
                break;
            case validate:
                break;
            case empty:
                break;
            case and:
                break;
            case or:
                break;
            case match_any:
                break;
            case match_all:
                break;
            case match_none:
                break;
            case count:
                break;
            case sum:
                break;
            case min:
                break;
            case not:
                break;
            case always_true:
                break;
            case always_false:
                break;
            case times:
                break;
            case equals:
                break;
            case not_equals:
                break;
            case is_null:
                break;
            case is_not_null:
                break;
            case as_a_number:
                break;
            case as_string:
                break;
            case as:
                break;
            case with:
                break;
            case minus:
                break;
            case plus:
                break;
            case after:
                break;
            case after_or_equals:
                break;
            case age_at:
                break;
            case before:
                break;
            case before_or_equals:
                break;
            case matches:
                break;
            case contains:
                break;
            case starts_with:
                break;
            case ends_with:
                break;
            case greater_than:
                break;
            case greater_or_equals:
                break;
            case xor:
                break;
            case is:
                break;
            case lesser_than:
                break;
            case lesser_or_equals:
                break;
            case has_not_size:
                break;
            case has_size:
                break;
            case is_empty:
                break;
            case is_not_empty:
                break;
            case length_is:
                break;
            case today:
                break;
            case today_plus:
                break;
            case today_minus:
                break;
            case first_day_of_this_month:
                break;
            case first_day_of_this_year:
                break;
            case last_day_of_this_month:
                break;
            case last_day_of_this_year:
                break;
            case first_day_of_month:
                break;
            case first_day_of_next_month:
                break;
            case first_day_of_year:
                break;
            case first_day_of_next_year:
                break;
            case last_day_of_month:
                break;
            case last_day_of_year:
                break;
        }
    }
    protected void write(String str) {
        try {
            ops.write(str.getBytes(StandardCharsets.UTF_8));
        } catch (IOException ioe) {
            throw new RuntimeException(ioe);
        }
    }

}
