/*
 * Copyright (C) by Courtanet, All Rights Reserved.
 */
package io.doov.js.ast;

import static io.doov.core.dsl.meta.DefaultOperator.*;
import static io.doov.core.dsl.meta.ElementType.FIELD;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.*;

import org.apache.commons.lang3.StringUtils;

import io.doov.core.dsl.meta.*;
import io.doov.core.dsl.meta.ast.AbstractAstVisitor;
import io.doov.core.dsl.meta.i18n.ResourceProvider;
import io.doov.core.dsl.meta.predicate.LeafPredicateMetadata;

public class AstJavascriptVisitor extends AbstractAstVisitor {

    protected final OutputStream ops;
    protected final ResourceProvider bundle;
    protected final Locale locale;

    private int parentheseDepth = 0;   // define the number of parenthesis to close before ending the rule rewriting
    private int startWithCount = 0;   // define the number of 'start_with' rule used for closing parenthesis purpose
    private int endWithCount = 0;     // define the number of 'start_with' rule used for closing parenthesis purpose
    private int useRegexp = 0;         // boolean as an int to know if we are in a regexp for closing parenthesis
    // purpose
    private int isMatch = 0;             // boolean as an int to know if we are in a matching rule for closing
    // parenthesis purpose
    private boolean isInATemporalFunction = false;
    private ArrayList<Integer> countDateOperators = new ArrayList<>(); // allow to count and separate date operator
    // on their respective arguments
    private static ArrayList<DefaultOperator> dateOpeElem = new ArrayList<>();

    public AstJavascriptVisitor(OutputStream ops, ResourceProvider bundle, Locale locale) {
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
        ArrayDeque<Element> stack = new ArrayDeque<>();    //using arrayDeque to store the fields
        final int[] chainDateOpe = new int[1];
        chainDateOpe[0] = -1;
        metadata.elements().forEach(element -> {
            switch (element.getType()) {
                case OPERATOR:
                    if (dateOpeElem.contains(element.getReadable())) {
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
                    if (element.getReadable() == as_a_number                       // checking for special cases
                            || element.getReadable() == as_string || dateOpeElem.contains(element.getReadable())) {
                        stack.addFirst(element);
                    } else {
                        if (element.getReadable() == not) {
                            stack.addFirst(element);
                        } else {
                            stack.add(element);
                        }
                    }
                    break;
                case STRING_VALUE:
                case FIELD:
                case VALUE:
                case TEMPORAL_UNIT:
                    stack.add(element);
                    break;
                case UNKNOWN:
                    write("/* Unknown " + element.toString() + "*/");
                    break;
                case PARENTHESIS_LEFT:
                case PARENTHESIS_RIGHT:
                    write("/*" + element.toString() + "*/");
                    break;
            }
        });
        manageStack(stack);
        while (parentheseDepth > 0) {
            write(")");
            parentheseDepth--;
        }
    }

    /**
     * This function manage the different parameters of the predicate
     *
     * @param stack A deque of the predicate parameters
     */
    private void manageStack(ArrayDeque<Element> stack) {
        while (stack.size() > 0) {
            Element e = stack.pollFirst();
            switch (e.getType()) {
                case FIELD:
                    write(e.toString());
                    break;
                case OPERATOR:
                    manageOperator((DefaultOperator) e.getReadable(), stack);
                    break;
                case VALUE:
                    if (isInATemporalFunction && e.getType() != FIELD) {
                        write("\'" + e.toString() + "\'");
                    } else if (e.toString().startsWith(" : ")) {
                        String values = e.toString().replace(" : ", "");
                        values = values.replace("[", "");
                        values = values.replace("]", "");
                        String[] valuesArray = values.split(", ");
                        values = "[";
                        if (StringUtils.isNumeric(e.toString())) {
                            for (int i = 0; i < valuesArray.length - 1; i++) {
                                values = values + valuesArray[i] + ", ";
                            }
                            values = values + valuesArray[valuesArray.length - 1];
                        } else {
                            for (int i = 0; i < valuesArray.length - 1; i++) {
                                values = values + "\'" + valuesArray[i] + "\', ";
                            }
                            values = values + "\'" + valuesArray[valuesArray.length - 1] + "\'";
                        }
                        values = values + "]";
                        write(values);
                    } else if (StringUtils.isNumeric(e.toString())) {
                        write(e.toString());
                    } else {
                        write(e.toString());
                    }
                    break;
                case STRING_VALUE:
                    if (useRegexp == 1) {
                        String tmp = e.toString();
                        if (isMatch == 1) {
                            isMatch = 0;
                        } else {
                            tmp = formatRegexp(tmp);
                        }
                        write(tmp);
                        if (startWithCount > 0) {
                            write(".*");
                            startWithCount--;
                        } else if (endWithCount > 0) {
                            write("$");
                            endWithCount--;
                        }
                        useRegexp = 0;
                    } else {
                        write("\'" + e.toString() + "\'");
                    }
                    break;
                case PARENTHESIS_LEFT:
                case PARENTHESIS_RIGHT:
                case UNKNOWN:
                    break;
            }
        }
    }

    /**
     * this method will write the javascript translation for the operator of the predicate
     *
     * @param element the default operator of the LeafMetadata
     * @param stack   the deque of the parameters not translated yet to Javascript predicate
     */
    private void manageOperator(DefaultOperator element, ArrayDeque<Element> stack) {
        ArrayDeque<Element> stackTmp = new ArrayDeque<>();
        switch (element) {
            case rule:
            case validate:
            case empty:
            case as:
                break;
            case with:
                manageStack(stack);
                break;
            case as_a_number:
                if (stack.size() > 0) {
                    write("parseInt(");
                    stackTmp.add(stack.pollFirst());
                    manageStack(stackTmp);
                    write(")");
                }
                break;
            case as_string:
                if (stack.size() > 0) {
                    write("String(");
                    stackTmp.add(stack.pollFirst());
                    manageStack(stackTmp);
                    write(")");
                }
                break;
            case and:
                write(" && ");
                break;
            case or:
                write(" || ");
                break;
            case count:
                break;
            case sum:
                break;
            case min:
                break;
            case not:
                write("!(");
                parentheseDepth++;
                break;
            case always_true:
                write("true");
                break;
            case always_false:
                write("false");
                break;
            case times:
                write(" * ");
                break;
            case when:
                break;
            case equals:
                boolean testDateOpe = false;
                if (dateOpeElem.contains(stack.getFirst().getReadable())) {
                    write(".isSame(");
                    testDateOpe = true;
                } else {
                    write(" == ");
                }
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                if (testDateOpe) {
                    write(")");
                }
                break;
            case not_equals:
                write(" != ");
                if (stack != null) {
                    stackTmp.add(stack.pollFirst());
                    manageStack(stackTmp);
                }
                break;
            case is_null:
                write(" === ( null || undefined || \"\" )");
                break;
            case is_not_null:
                write(" !== ( null && undefined && \"\" )");
                break;
            case minus:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").subtract(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(",\'" + stack.pollFirst().toString() + "\')");
                break;
            case plus:
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").add(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(",\'" + stack.pollFirst().toString() + "\')");
                break;
            case after:
                isInATemporalFunction = true;
                write("moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(").isAfter(moment(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(")");
                parentheseDepth++;
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
                parentheseDepth++;
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
                parentheseDepth++;
                isInATemporalFunction = false;
                break;
            case before_or_equals:
                isInATemporalFunction = true;
                write("moment(" + stack.pollFirst().toString() +
                        ").isSameOrBefore(\'" + stack.pollFirst().toString() + "\'");
                parentheseDepth++;
                isInATemporalFunction = false;
                break;
            case matches:
                write(".match(/");
                parentheseDepth++;
                useRegexp = 1;
                isMatch = 1;
                break;
            case match_any:
                write(".some(function(element){\n" +
                        "return ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".indexOf(element) >= 0 ;\n" +
                        "})");
                break;
            case match_all:
                write(".every(function(element){\n" +
                        "return ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".every(function(elt){ return elt.match(element);});\n})");
                break;
            case match_none:
                write(".every(function(element){\n" +
                        "return ");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(".indexOf(element) < 0 ;\n" +
                        "})");
                break;
            case contains:
                write(".some(function(element){\n" +
                        "return element.match(");
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write(");\n" +
                        "})");
                break;
            case starts_with:
                write(".some(function(element){\n" +
                        "return element.match(/^");
                startWithCount++;
                parentheseDepth++;
                useRegexp = 1;
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write("/)}");
                break;
            case ends_with:
                write(".some(function(element){\n" +
                        "return element.match(/.*");
                endWithCount++;
                parentheseDepth++;
                useRegexp = 1;
                stackTmp.add(stack.pollFirst());
                manageStack(stackTmp);
                write("/)}");

                break;
            case greater_than:
                write(" > ");
                if (stack != null && stack.size() > 0) {
                    write(stack.pollFirst().toString());
                }
                break;
            case greater_or_equals:
                write(" >= ");
                if (stack != null && stack.size() > 0) {
                    write(stack.pollFirst().toString());
                }
                break;
            case xor:
                break;
            case is:
                write(" === ");

                break;
            case lesser_than:
                write(" < ");
                if (stack != null && stack.size() > 0) {
                    write(stack.pollFirst().toString());
                }
                break;
            case lesser_or_equals:
                write(" <= ");
                if (stack != null && stack.size() > 0) {
                    write(stack.pollFirst().toString());
                }
                break;
            case has_not_size:
                write(".length != ");
                break;
            case has_size:
                write(".length == ");
                break;
            case is_empty:
                write(".length == 0");
                break;
            case is_not_empty:
                write(".length != 0");
                break;
            case length_is:
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

    /**
     * XOR operator construction and writing
     *
     * @param leftMD  left Metadata of the XOR predicate
     * @param rightMD right Metadata of the XOR predicate
     */
    private void manageXOR(Metadata leftMD, Metadata rightMD) {
        write("(!" + leftMD + " && " + rightMD + ") || (" + leftMD + " && !" + rightMD + ")");
    }

    @Override
    public void startWhen(WhenMetadata metadata, int depth) {
        write("if(");
    }

    @Override
    public void endWhen(WhenMetadata metadata, int depth) {
        while (parentheseDepth > 0) {
            write(")");                 //closing parenthesis
            parentheseDepth--;
        }
        write("){ true;}else{ false;}\n");
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

    protected void write(String str) {
        try {
            ops.write(str.getBytes(StandardCharsets.UTF_8));
        } catch (IOException ioe) {
            throw new RuntimeException(ioe);
        }
    }
}
