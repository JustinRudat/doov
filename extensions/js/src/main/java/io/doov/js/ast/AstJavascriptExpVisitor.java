/*
 * Copyright (C) by Courtanet, All Rights Reserved.
 */
package io.doov.js.ast;

import static io.doov.core.dsl.meta.DefaultOperator.*;
import static io.doov.core.dsl.meta.ElementType.FIELD;
import static org.apache.commons.lang3.StringUtils.isNumeric;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.*;

import org.apache.commons.lang3.StringUtils;

import io.doov.core.dsl.meta.*;
import io.doov.core.dsl.meta.ast.AbstractAstVisitor;
import io.doov.core.dsl.meta.i18n.ResourceProvider;
import io.doov.core.dsl.meta.predicate.LeafPredicateMetadata;

public class AstJavascriptExpVisitor extends AbstractAstVisitor {

    protected final OutputStream ops;
    protected final ResourceProvider bundle;
    protected final Locale locale;

    private static final ArrayList<DefaultOperator> dateOpeElem = new ArrayList<>();
    private boolean startWithCount = false;   // define the number of 'start_with' rule used for closing parenthesis
    // purpose
    private boolean endWithCount = false;     // define the number of 'start_with' rule used for closing parenthesis
    // purpose
    private boolean useRegexp = false;         // boolean as an int to know if we are in a regexp for closing
    // parenthesis
    private boolean isMatch = false;             // boolean as an int to know if we are in a matching rule for closing
    private boolean testDateOpe = false;
    private boolean isInATemporalFunction = false;
    private ArrayList<Integer> countDateOperators = new ArrayList<>(); // allow to count and separate date operator
    // on their respective arguments

    private int parenthesisDepth = 0;

    public AstJavascriptExpVisitor(OutputStream ops, ResourceProvider bundle, Locale locale) {
        this.ops = ops;
        this.bundle = bundle;
        this.locale = locale;
        initializeDateOperator();
    }

    private void initializeDateOperator() {
        dateOpeElem.add(plus);
        dateOpeElem.add(minus);
        dateOpeElem.add(today);
        dateOpeElem.add(after);
        dateOpeElem.add(before);
        dateOpeElem.add(after_or_equals);
        dateOpeElem.add(before_or_equals);
        dateOpeElem.add(today_minus);
        dateOpeElem.add(today_minus);
        dateOpeElem.add(first_day_of_month);
        dateOpeElem.add(first_day_of_year);
        dateOpeElem.add(first_day_of_next_month);
        dateOpeElem.add(first_day_of_next_year);
        dateOpeElem.add(first_day_of_this_month);
        dateOpeElem.add(first_day_of_this_year);
        dateOpeElem.add(last_day_of_month);
        dateOpeElem.add(last_day_of_year);
        dateOpeElem.add(last_day_of_this_month);
        dateOpeElem.add(last_day_of_this_year);
    }

    @Override
    public void startLeaf(LeafPredicateMetadata<?> metadata, int depth) {
        ArrayDeque<Element> stack = new ArrayDeque<>();
        final int[] chainDateOpe = new int[1];
        chainDateOpe[0] = -1;
        metadata.elements().forEach(
                elt -> {
                    switch (elt.getType()) {
                        case OPERATOR:
                            if(elt.getReadable() == with){
                                break;
                            }
                            if (dateOpeElem.contains(elt.getReadable())) {
                                if (chainDateOpe[0] == -1) {
                                    chainDateOpe[0] = 0;
                                    countDateOperators.add(1);
                                } else {
                                    countDateOperators.set(countDateOperators.size() - 1,
                                            countDateOperators.get(countDateOperators.size() - 1) + 1);
                                }
                            } else if (chainDateOpe[0] != -1) {
                                chainDateOpe[0] = -1;
                            }
                            stack.addFirst(elt);
                            break;
                        case FIELD:
                        case VALUE:
                        case STRING_VALUE:
                        case PARENTHESIS_LEFT:
                        case PARENTHESIS_RIGHT:
                        case TEMPORAL_UNIT:
                        case UNKNOWN:
                            stack.add(elt);
                            break;
                    }
                }
        );
        manageStack(stack);
    }

    private void manageStack(ArrayDeque<Element> stack) {
        String values;
        while (stack.size() > 0) {
            Element e = stack.pollFirst();
            switch (e.getType()) {
                case FIELD:
                    if(isInATemporalFunction){
                        write("moment(");
                        write(e.toString());
                        write(")");
                    }else {
                        write(e.toString());
                    }
                    break;
                case OPERATOR:
                    manageOperator((DefaultOperator) e.getReadable(), stack);
                    break;
                case VALUE:
                    values = e.toString();
                    if (isInATemporalFunction && e.getType() != FIELD) {
                        write("\'" + values + "\'");
                    } else if (values.startsWith(" : ")) {
                        manageTabValues(e.toString().replace(" : ", ""));
                    } else if (StringUtils.isNumeric(e.toString())) {
                        write(e.toString());
                    } else {
                        write(e.toString());
                    }
                    break;
                case STRING_VALUE:
                    values = e.toString();
                    if (useRegexp) {
                        String tmp = e.toString();
                        if (isMatch) {
                            isMatch = false;
                        } else {
                            tmp = formatRegexp(tmp);
                        }
                        write(tmp);
                        if (startWithCount) {
                            write(".*");
                        } else if (endWithCount) {
                            write("$");
                        }
                    } else if (values.startsWith(" : ")) {
                        manageTabValues(values.replace(" : ", ""));
                    } else {
                        write("\'" + values + "\'");
                    }
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
        }
    }

    public void manageTabValues(String values) {
        values = values.replace("[", "");
        values = values.replace("]", "");
        String[] valuesArray = values.split(", ");
        values = "[";
        for (int i = 0; i < valuesArray.length - 1; i++) {
            if (isNumeric(valuesArray[i])) {
                values += valuesArray[i] + ", ";
            } else {
                values += "\'" + valuesArray[i] + "\', ";
            }
        }
        if (isNumeric(valuesArray[valuesArray.length - 1])) {
            values += valuesArray[valuesArray.length - 1] + "]";
        } else {
            values += "\'" + valuesArray[valuesArray.length - 1] + "\']";
        }
        write(values);
        values = "";
    }

    private void manageIterableField(ArrayDeque<Element> stack, ArrayDeque<Element> stackTmp) {
        if (stack.getFirst().getReadable().toString().contains("IterableFieldInfo")) {
            stackTmp.add(stack.pollFirst());
            manageStack(stackTmp);
        } else {
            write("[");
            stackTmp.add(stack.pollFirst());
            manageStack(stackTmp);
            write("]");
            useRegexp = true;
        }
    }

    private void manageOperator(DefaultOperator operator, ArrayDeque<Element> stack) {
        ArrayDeque<Element> stackTmp = new ArrayDeque<>();
        switch (operator) {
            case rule:
                break;
            case validate:
                break;
            case empty:
                break;
            case and:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" && ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case or:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" || ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case match_any:
                manageIterableField(stack, stackTmp);
                write(".some(function(element){\n return ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".indexOf(element) >= 0 ;\n})");
                useRegexp = false;
                break;
            case match_all:
                manageIterableField(stack, stackTmp);
                write(".every(function(element){\n" +
                        "return ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".every(function(elt){ return elt.match(element);});\n})");
                useRegexp = false;
                break;
            case match_none:
                manageIterableField(stack, stackTmp);
                write(".every(function(element){\n" +
                        "return ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".indexOf(element) < 0;})");
                useRegexp = false;
                break;
            case count:
                break;
            case sum:
                break;
            case min:
                break;
            case not:
                write("!(");
                parenthesisDepth++;
                break;
            case always_true:
                write("true");
                break;
            case always_false:
                write("false");
                break;
            case times:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" * ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case when:
                break;
            case equals:
                if (dateOpeElem.contains(stack.getFirst().getReadable())) {
                    stackTmp = stack.clone();
                    stack.clear();
                    stack.add(stackTmp.pollLast());
                    manageStack(stackTmp);
                    testDateOpe = true;
                } else {
                    stackTmp.add(stack.pollFirst());
                    manageStack(stackTmp);
                }
                if (testDateOpe) {
                    write(".isSame(");
                } else {
                    write(" == ");
                }
                if (testDateOpe) {
                    write("\'");
                }
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                if (testDateOpe) {
                    write("\')");
                    testDateOpe = false;
                }
                break;
            case not_equals:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" != ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case is_null:
                write("( null || undefined || \"\" ) == ");
                break;
            case is_not_null:
                write("( null && undefined && \"\" ) != ");
                break;
            case as_a_number:
                write("parseInt(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(")");
                break;
            case as_string:
                write("String(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(")");
                break;
            case as:
                break;
            case with:
                manageStack(stack);
                break;
            case minus:
                isInATemporalFunction = true;
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").subtract(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(",\'" + stack.pollFirst().toString() + "\')");
                testDateOpe = true;
                isInATemporalFunction = false;
                break;
            case plus:
                isInATemporalFunction = true;
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".add(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(",\'" + stack.pollFirst().toString() + "\')");
                testDateOpe = true;
                isInATemporalFunction = false;
                break;
            case after:
                isInATemporalFunction = true;
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".isAfter(moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(")");
                parenthesisDepth++;
                isInATemporalFunction = false;
                break;
            case after_or_equals:
                isInATemporalFunction = true;
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").isSameOrAfter(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                parenthesisDepth++;
                isInATemporalFunction = false;
                break;
            case age_at:
                isInATemporalFunction = true;
                write("Math.round(Math.abs(moment(");               // using Math.round(...)
                stackTmp.add(stack.pollFirst());                        // ex : diff(31may,31may + 1month) = 0.96
                manageStack(stackTmp);
                write(")");
                formatAgeAtOperator(stack);
                write(".diff(");                                   //Math.abs so the date order doesn't matter
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(")");
                formatAgeAtOperator(stack);
                write(", \'years\')))");
                isInATemporalFunction = false;
                break;
            case before:
                isInATemporalFunction = true;
                write("moment(" + stack.pollFirst().toString() +
                        ").isBefore(" + stack.pollFirst().toString());
                parenthesisDepth++;
                isInATemporalFunction = false;
                break;
            case before_or_equals:
                isInATemporalFunction = true;
                write("moment(" + stack.pollFirst().toString() +
                        ").isSameOrBefore(\'" + stack.pollFirst().toString() + "\'");
                parenthesisDepth++;
                isInATemporalFunction = false;
                break;
            case matches:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".match(/");
                useRegexp = true;
                isMatch = true;
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write("/)");
                break;
            case contains:
                manageIterableField(stack, stackTmp);
                write(".some(function(element){\n" +
                        "return element.match(");
                if (useRegexp) {
                    write("/.*");
                }
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                if (useRegexp) {
                    write(".*/");
                }
                write(");})");
                useRegexp = false;
                break;
            case starts_with:
                manageIterableField(stack, stackTmp);
                write(".some(function(element){\n" +
                        "return element.match(/^");
                startWithCount = true;
                parenthesisDepth++;
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write("/)}");
                useRegexp = false;
                startWithCount = false;
                break;
            case ends_with:
                manageIterableField(stack, stackTmp);
                write(".some(function(element){\n" +
                        "return element.match(/.*");
                endWithCount = true;
                parenthesisDepth++;
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write("/)}");
                useRegexp = false;
                endWithCount = false;
                break;
            case greater_than:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" > ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case greater_or_equals:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" >= ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case xor:
                break;
            case is:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" === ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case lesser_than:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" < ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case lesser_or_equals:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(" <= ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                break;
            case has_not_size:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".length != ");
                break;
            case has_size:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".length == ");
                break;
            case is_empty:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".length == 0");
                break;
            case is_not_empty:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".length != 0");
                break;
            case length_is:
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".length");
                break;
            case today:
                write("moment(moment().format(\"YYYY-MM-DD\"))");
                break;
            case today_plus:
                write("moment(moment().format(\"YYYY-MM-DD\")).add(");
                break;
            case today_minus:
                write("moment(moment().format(\"YYYY-MM-DD\")).subtract(");
                break;
            case first_day_of_this_month:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").startOf('month')");
                break;
            case first_day_of_this_year:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").startOf('year')");
                break;
            case last_day_of_this_month:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").endOf('month')");
                break;
            case last_day_of_this_year:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").endOf('year')");
                break;
            case first_day_of_month:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").startOf('month')");
                break;
            case first_day_of_next_month:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").add(1,'month').startOf('month')");
                break;
            case first_day_of_year:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").startOf('year')");
                break;
            case first_day_of_next_year:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").add(1,'year').startOf('year')");
                break;
            case last_day_of_month:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").endOf('month')");
                break;
            case last_day_of_year:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").endOf('year')");
                break;
        }
    }

    @Override
    public void startWhen(WhenMetadata metadata, int depth) {
        write("if(");
    }

    @Override
    public void endWhen(WhenMetadata metadata, int depth) {
        while (parenthesisDepth > 0) {
            write(")");
            parenthesisDepth--;
        }
        write("){ true; }else{ false; }\n");
    }

    /**
     * XOR operator construction and writing
     *
     * @param leftMD  left Metadata of the XOR predicate
     * @param rightMD right Metadata of the XOR predicate
     */
    private void manageXOR(Metadata leftMD, Metadata rightMD) {
        write("(!" + leftMD + " && " + rightMD + ") || (" + leftMD + " && !" + rightMD + ")");
    }

    /**
     * age_at operator specials cases for the parameter in moment.js
     *
     * @param stack the deque of the parameters not translated yet to Javascript predicate
     */
    private void formatAgeAtOperator(ArrayDeque<Element> stack) {
        if (countDateOperators.size() > 0) {
            while (countDateOperators.size() > 0 && countDateOperators.get(0) > 0) {
                ArrayDeque<Element> stackTmp = new ArrayDeque<>();
                if (stack.getFirst().getReadable() == with || stack.getFirst().getReadable() == plus
                        || stack.getFirst().getReadable() == minus) {
                    if (stack.getFirst().getReadable() == with) {
                        stack.pollFirst();
                        stackTmp.add(stack.pollFirst());
                        manageStack(stackTmp);
                    } else {                                      // working on plus and minus operators
                        Element ope = stack.pollFirst();        // need the three first elements of the stack to manage
                        Element duration = stack.pollFirst();   // these operators
                        Element unit = stack.pollFirst();
                        stackTmp.add(ope);
                        stackTmp.add(duration);
                        stackTmp.add(unit);
                        manageStack(stackTmp);
                    }
                    countDateOperators.set(0, countDateOperators.get(0) - 1);
                    if (countDateOperators.size() > 0 && countDateOperators.get(0) == 0) {
                        countDateOperators.remove(0);
                    }
                } else {
                    break;
                }
            }
        }
    }

    protected void write(String str) {
        try {
            ops.write(str.getBytes(StandardCharsets.UTF_8));
        } catch (IOException ioe) {
            throw new RuntimeException(ioe);
        }
    }

    /**
     * replace in a String object the special characters |, ., ^, $, (, ), [, ], -, {, }, ?, *, + and /.
     *
     * @param reg the String to format for usage as a regular expression
     * @return the formatted String
     */
    private String formatRegexp(String reg) {
        reg = reg.replace("|", "\\|");
        reg = reg.replace(".", "\\.");
        reg = reg.replace("^", "\\^");
        reg = reg.replace("$", "\\$");
        reg = reg.replace("(", "\\(");
        reg = reg.replace(")", "\\)");
        reg = reg.replace("[", "\\[");
        reg = reg.replace("]", "\\]");
        reg = reg.replace("-", "\\-");
        reg = reg.replace("{", "\\{");
        reg = reg.replace("}", "\\}");
        reg = reg.replace("?", "\\?");
        reg = reg.replace("*", "\\*");
        reg = reg.replace("+", "\\+");
        reg = reg.replace("/", "\\/");
        return reg;
    }

}
