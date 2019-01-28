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
import java.util.ArrayList;
import java.util.Locale;

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
    private Metadata leafMetadata;

    private int parenthesisDepth = 0;
    private int indiceFirstParam = -1;

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
        leafMetadata = metadata;
        ArrayList<Element> stack = new ArrayList<>();
        final int[] chainDateOpe = new int[1];
        chainDateOpe[0] = -1;
        metadata.elements().forEach(
                elt -> {
                    switch (elt.getType()) {
                        case OPERATOR:
                            if (elt.getReadable() == with) {
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
                            stack.add(indiceFirstParam, elt);
                            break;
                        case FIELD:
                        case VALUE:
                        case STRING_VALUE:
                        case PARENTHESIS_LEFT:
                        case PARENTHESIS_RIGHT:
                        case TEMPORAL_UNIT:
                        case UNKNOWN:
                            if (indiceFirstParam == -1) {
                                indiceFirstParam = stack.size();
                            }
                            stack.add(elt);
                            break;
                    }
                }
        );
        manageStack(stack);
    }

    private void manageStack(ArrayList<Element> stack) {
        String values;
        while (stack.size() > 0) {
            Element e = stack.remove(0);
            switch (e.getType()) {
                case FIELD:
                    if (isInATemporalFunction) {
                        write("moment(");
                        write(e.toString());
                        write(")");
                    } else {
                        write(e.toString());
                    }
                    break;
                case OPERATOR:
                    manageOperator(e, stack);
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
    }

    private void manageIterableField(ArrayList<Element> stack, ArrayList<Element> stackTmp) {
        if (stack.get(0).getReadable().toString().contains("IterableFieldInfo")) {
            stackTmp.add(stack.remove(0));
            manageStack(stackTmp);
        } else {
            write("[");
            stackTmp.add(stack.remove(0));
            manageStack(stackTmp);
            write("]");
            useRegexp = true;
        }
    }

    private void manageOperator(Element element, ArrayList<Element> stack) {
        ArrayList<Element> stackTmp = new ArrayList<>();
        DefaultOperator operator = (DefaultOperator) element.getReadable();
        switch (operator) {
            case rule:
                break;
            case validate:
                break;
            case empty:
                break;
            case and:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" && ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                break;
            case or:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" || ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                break;
            case match_any:
                manageIterableField(stack, stackTmp);
                write(".some(function(element){\n return ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".indexOf(element) >= 0 ;\n})");
                useRegexp = false;
                break;
            case match_all:
                manageIterableField(stack, stackTmp);
                write(".every(function(element){\n" +
                        "return ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".every(function(elt){ return elt.match(element);});\n})");
                useRegexp = false;
                break;
            case match_none:
                manageIterableField(stack, stackTmp);
                write(".every(function(element){\n" +
                        "return ");
                stackTmp.add(stack.remove(0));
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
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" * ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                break;
            case when:
                break;
            case equals:
                if (dateOpeElem.contains(stack.get(0).getReadable())) {
                    stackTmp = (ArrayList<Element>) stack.clone();
                    stack.clear();
                    stack.add(stackTmp.remove(stack.size() - 1));
                    manageStack(stackTmp);
                    testDateOpe = true;
                } else {
                    stackTmp.add(stack.remove(0));
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
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                if (testDateOpe) {
                    write("\')");
                    testDateOpe = false;
                }
                break;
            case not_equals:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" != ");
                stackTmp.add(stack.remove(0));
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
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(")");
                break;
            case as_string:
                write("String(");
                stackTmp.add(stack.remove(0));
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
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").subtract(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(",\'" + stack.remove(0).toString() + "\')");
                testDateOpe = true;
                isInATemporalFunction = false;
                break;
            case plus:
                isInATemporalFunction = true;
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".add(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(",\'" + stack.remove(0).toString() + "\')");
                testDateOpe = true;
                isInATemporalFunction = false;
                break;
            case after:
                isInATemporalFunction = true;
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".isAfter(moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(")");
                parenthesisDepth++;
                isInATemporalFunction = false;
                break;
            case after_or_equals:
                isInATemporalFunction = true;
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").isSameOrAfter(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                parenthesisDepth++;
                isInATemporalFunction = false;
                break;
            case age_at:
                isInATemporalFunction = true;
                write("Math.round(Math.abs(moment(");               // using Math.round(...)
                stackTmp.add(stack.remove(0));                        // ex : diff(31may,31may + 1month) = 0.96
                manageStack(stackTmp);
                write(")");
                formatAgeAtOperator(stack);
                write(".diff(");                                   //Math.abs so the date order doesn't matter
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(")");
                formatAgeAtOperator(stack);
                write(", \'years\')))");
                isInATemporalFunction = false;
                break;
            case before:
                isInATemporalFunction = true;
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".isBefore(moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(")");
                parenthesisDepth++;
                isInATemporalFunction = false;
                break;
            case before_or_equals:
                isInATemporalFunction = true;
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").isSameOrBefore(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                parenthesisDepth++;
                isInATemporalFunction = false;
                break;
            case matches:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".match(/");
                useRegexp = true;
                isMatch = true;
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write("/)");
                break;
            case contains:
                if (isSiblingIterable(element, false)) {
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                    write(".every(function(element){ return ");
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                    write(".some(function(elt){ return elt.match(element);});})");
                } else {
                    manageIterableField(stack, stackTmp);
                    write(".some(function(element){\n" +
                            "return element.match(");
                    if (useRegexp) {
                        write("/.*");
                    }
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                    if (useRegexp) {
                        write(".*/");
                    }
                    write(");})");
                    useRegexp = false;
                }
                break;
            case starts_with:
                manageIterableField(stack, stackTmp);
                write(".some(function(element){\n" +
                        "return element.match(/^");
                startWithCount = true;
                parenthesisDepth++;
                stackTmp.add(stack.remove(0));
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
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write("/)}");
                useRegexp = false;
                endWithCount = false;
                break;
            case greater_than:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" > ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                break;
            case greater_or_equals:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" >= ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                break;
            case xor:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" ? !");
                stackTmp.add(stack.get(0));
                manageStack(stackTmp);
                write(" : ");
                break;
            case is:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" === ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                break;
            case lesser_than:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" < ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                break;
            case lesser_or_equals:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(" <= ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                break;
            case has_not_size:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".length != ");
                break;
            case has_size:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".length == ");
                break;
            case is_empty:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".length == 0");
                break;
            case is_not_empty:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".length != 0");
                break;
            case length_is:
                stackTmp.add(stack.remove(0));
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
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").startOf('month')");
                break;
            case first_day_of_this_year:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").startOf('year')");
                break;
            case last_day_of_this_month:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").endOf('month')");
                break;
            case last_day_of_this_year:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").endOf('year')");
                break;
            case first_day_of_month:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").startOf('month')");
                break;
            case first_day_of_next_month:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").add(1,'month').startOf('month')");
                break;
            case first_day_of_year:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").startOf('year')");
                break;
            case first_day_of_next_year:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").add(1,'year').startOf('year')");
                break;
            case last_day_of_month:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").endOf('month')");
                break;
            case last_day_of_year:
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").endOf('year')");
                break;
        }
    }

    private boolean isSiblingIterable(Element element, boolean before) {
        ArrayList<Element> flatData = (ArrayList<Element>) leafMetadata.flatten();
        int elementIndex = flatData.indexOf(element);
        if (elementIndex > 0 && elementIndex < flatData.size() - 1) {
            if (before) {
                if (flatData.get(elementIndex - 1).getReadable().toString().contains("Iterable")) {
                    return true;
                }
            } else {
                Element eltTmp = flatData.get(elementIndex + 1);
                if (eltTmp.getReadable().toString().contains("Iterable") || eltTmp.toString().startsWith(" : ")) {
                    return true;
                }
            }
        }
        return false;
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
    private void formatAgeAtOperator(ArrayList<Element> stack) {
        if (countDateOperators.size() > 0) {
            while (countDateOperators.size() > 0 && countDateOperators.get(0) > 0) {
                ArrayList<Element> stackTmp = new ArrayList<>();
                if (stack.get(0).getReadable() == with || stack.get(0).getReadable() == plus
                        || stack.get(0).getReadable() == minus) {
                    if (stack.get(0).getReadable() == with) {
                        stack.remove(0);
                        stackTmp.add(stack.remove(0));
                        manageStack(stackTmp);
                    } else {                                      // working on plus and minus operators
                        Element ope = stack.remove(0);        // need the three first elements of the stack to manage
                        Element duration = stack.remove(0);   // these operators
                        Element unit = stack.remove(0);
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
