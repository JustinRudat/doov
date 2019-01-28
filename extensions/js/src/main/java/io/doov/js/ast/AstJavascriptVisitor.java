/*
 * Copyright (C) by Courtanet, All Rights Reserved.
 */
package io.doov.js.ast;

import static io.doov.core.dsl.meta.DefaultOperator.*;
import static org.apache.commons.lang3.StringUtils.isNumeric;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.*;

import org.apache.commons.lang3.StringUtils;

import io.doov.core.dsl.meta.*;
import io.doov.core.dsl.meta.ast.AbstractAstVisitor;
import io.doov.core.dsl.meta.i18n.ResourceProvider;
import io.doov.core.dsl.meta.predicate.*;

public class AstJavascriptVisitor extends AbstractAstVisitor {

    protected final OutputStream ops;
    protected final ResourceProvider bundle;
    protected final Locale locale;

    private int parentheseDepth = 0;   // define the number of parenthesis to close before ending the rule rewriting
    private boolean startWithCount = false;   // define the number of 'start_with' rule used for closing parenthesis
    // purpose
    private boolean endWithCount = false;     // define the number of 'start_with' rule used for closing parenthesis
    // purpose
    private boolean useRegexp = false;         // boolean as an int to know if we are in a regexp for closing
    // parenthesis purpose
    private boolean isMatch = false;             // boolean as an int to know if we are in a matching rule for
    // closing parenthesis purpose
    private boolean isTemporalPredicate = false;
    private boolean startedChaining = false;
    private int indiceFirstArg = -1;
    private ArrayList<Integer> countDateOperators = new ArrayList<>(); // allow to count and separate date operator
    // on their respective arguments
    private ArrayList<DefaultOperator> dateOpeElem = new ArrayList<>();
    private Metadata leafMetadata;

    public AstJavascriptVisitor(OutputStream ops, ResourceProvider bundle, Locale locale) {
        this.ops = ops;
        this.bundle = bundle;
        this.locale = locale;
        initializeDateOperator();
    }

    private void initializeDateOperator() {
        dateOpeElem.add(plus);
        dateOpeElem.add(age_at);
        dateOpeElem.add(minus);
        dateOpeElem.add(today_minus);
        dateOpeElem.add(today_minus);
        dateOpeElem.add(first_day_of_month);
        dateOpeElem.add(first_day_of_year);
        dateOpeElem.add(last_day_of_month);
        dateOpeElem.add(last_day_of_year);
        dateOpeElem.add(after);
        dateOpeElem.add(after_or_equals);
        dateOpeElem.add(before_or_equals);
        dateOpeElem.add(before);
    }

    @Override
    public void startBinary(BinaryPredicateMetadata metadata, int depth) {
        write("(");
    }

    @Override
    public void afterChildBinary(BinaryPredicateMetadata metadata, Metadata child, boolean hasNext, int depth) {
        if (hasNext) {
            switch ((DefaultOperator) metadata.getOperator()) {
                case and:
                    write(" && ");
                    break;
                case or:
                    write(" || ");
                    break;
                case xor:
                    manageXOR(metadata.getLeft(), metadata.getRight());
                    break;
                case greater_than:
                    write(" > ");
                    break;
                case greater_or_equals:
                    write(" >= ");
                    break;
                case lesser_than:
                    write(" < ");
                    break;
                case lesser_or_equals:
                    write(" <= ");
                case equals:
                    write(" == ");
                    break;
                case not_equals:
                    write(" != ");
                    break;
            }
        }
    }

    @Override
    public void endBinary(BinaryPredicateMetadata metadata, int depth) {
        write(")");
    }

    @Override
    public void startNary(NaryPredicateMetadata metadata, int depth) {
        if (metadata.getOperator() == match_none) {
            write("!");                             // for predicate [a,b,c] will translate as (!a && !b && !c)
        }
        if (metadata.getOperator() == count || metadata.getOperator() == sum) {
            write("[");                             // opening a list to use count or sum on
        }
        if (metadata.getOperator() == min) {
            write("Math.min.apply(null,[");         // using JS Math module to apply min on a list, opening the list
        }
    }

    @Override
    public void afterChildNary(NaryPredicateMetadata metadata, Metadata child, boolean hasNext, int depth) {
        if (hasNext) {
            switch ((DefaultOperator) metadata.getOperator()) {
                case match_any:
                    write(" || ");                       // using 'or' operator to match any of the predicate given
                    break;
                case match_all:
                    write(" && ");                       // using 'and' operator for match all
                    break;
                case match_none:
                    write(" && !");                      // 'and not' for match none
                    break;
                case min:
                case sum:
                case count:
                    write(", ");                         // separating the list values
                    break;
            }
        }
    }

    @Override
    public void endNary(NaryPredicateMetadata metadata, int depth) {
        if (metadata.getOperator() == count) {
            write("].reduce(function(acc,val){if(val){return acc+1;}return acc;},0)");
        }                                                       // using reduce method to count with an accumulator
        if (metadata.getOperator() == min) {
            write("])");                                    // closing the value list
        }
        if (metadata.getOperator() == sum) {
            write("].reduce(function(acc,val){ return acc+val;},0)");
        }                                                       // using reduce method to sum the value
    }

    @Override
    public void startLeaf(LeafPredicateMetadata<?> metadata, int depth) {
        leafMetadata = metadata;
        ArrayList<Element> stack = new ArrayList<>();    //using arrayDeque to store the fields
        final int[] chainDateOpe = new int[1];
        chainDateOpe[0] = -1;
        metadata.elements().forEach(element -> {
            switch (element.getType()) {
                case OPERATOR:
                    DefaultOperator operator = (DefaultOperator) element.getReadable();
                    if (dateOpeElem.contains(operator)) {
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

                    if (operator == as_a_number || operator == xor                // checking for special cases
                            || operator == as_string || dateOpeElem.contains(operator) || operator == not) {
                        if(indiceFirstArg == -1) {
                            stack.add(0, element);
                        } else {
                            stack.add(indiceFirstArg, element);
                            indiceFirstArg++;
                        }
                    } else {
                        stack.add(element);
                        if(indiceFirstArg == -1){
                            indiceFirstArg = stack.size() - 1;
                        }
                    }
                    break;
                case STRING_VALUE:
                case FIELD:
                case VALUE:
                case TEMPORAL_UNIT:
                    stack.add(element);
                    if(indiceFirstArg == -1){
                        indiceFirstArg = stack.size() - 1;
                    }
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

    @Override
    public void beforeChildUnary(UnaryPredicateMetadata metadata, Metadata child, int depth) {
        manageOperator((Element) metadata.getOperator(), null);

    }

    @Override
    public void endUnary(UnaryPredicateMetadata metadata, int depth) {
        write(")");
    }

    /**
     * This function manage the different parameters of the predicate
     *
     * @param stack A deque of the predicate parameters
     */
    private void manageStack(ArrayList<Element> stack) {
        while (stack.size() > 0) {
            Element e = stack.remove(0);
            switch (e.getType()) {
                case FIELD:
                    boolean isContains = false;
                    if (isTemporalPredicate || e.getReadable().toString().contains("Date")) {
                        write("moment(");
                        write(e.toString());
                        write(")");
                        isTemporalPredicate = true;
                    } else {
                        if (stack.size() > 0 && stack.get(0).getReadable() == contains
                                && !(e.getReadable().toString().contains("Iterable"))) {
                            isContains = true;
                            write("[");
                        }
                        write(e.toString());
                        if (isContains) {
                            write("]");
                        }
                    }
                    break;
                case OPERATOR:
                    manageOperator(e, stack);
                    break;
                case VALUE:
                    if (e.toString().startsWith(" : ")) {
                        write(manageTabValues(e.toString().replace(" : ", "")));
                    } else if (StringUtils.isNumeric(e.toString())) {
                        write(e.toString());
                    } else {
                        if (isTemporalPredicate) {
                            isTemporalPredicate = false;
                            if(e.getReadable().toString().contains("Date")){
                                write("moment(" + e.toString() + ")");
                            } else {
                                write("moment(\'" + e.toString() + "\')");
                            }
                        } else {
                            write(e.toString());
                        }
                    }
                    break;
                case STRING_VALUE:
                    if (e.toString().startsWith(" : ")) {
                        write(manageTabValues(e.toString().replace(" : ", "")));
                    } else if (useRegexp) {
                        String tmp = e.toString();
                        if (isMatch) {
                            isMatch = false;
                        } else {
                            tmp = formatRegexp(tmp);
                        }
                        write(tmp);
                        if (startWithCount) {
                            write(".*");
                            startWithCount = false;
                        } else if (endWithCount) {
                            write("$");
                            endWithCount = false;
                        }
                        write("/");
                        useRegexp = false;
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
    private void manageOperator(Element element, ArrayList<Element> stack) {
        ArrayList<Element> stackTmp = new ArrayList<>();
        DefaultOperator operator = (DefaultOperator) element.getReadable();
        switch (operator) {
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
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                    write(")");
                }
                break;
            case as_string:
                if (stack.size() > 0) {
                    write("String(");
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                    write(")");
                }
                break;
            case not:
                write("!(");
                manageStack(stack);
                write(")");
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
            case equals:
                boolean testDateOpe = false;
                if (isTemporalPredicate) {
                    write(".isSame(");
                    testDateOpe = true;
                } else {
                    write(" == ");
                }
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                if (testDateOpe) {
                    isTemporalPredicate = false;
                    write(")");
                }
                break;
            case not_equals:
                write(" != ");
                if (stack != null) {
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                }
                break;
            case is_null:
                write(" === ( null || undefined || \"\" ) ");
                break;
            case is_not_null:
                write(" !== ( null && undefined && \"\" ) ");
                break;
            case minus:
                isTemporalPredicate = true;
                indiceFirstArg--;
                if (!startedChaining) {
                    startedChaining = true;
                    stackTmp.add(stack.remove(indiceFirstArg));
                    manageStack(stackTmp);
                }
                write(".subtract(");
                decreaseCount(countDateOperators);
                if (countDateOperators.get(0) == 0) {
                    countDateOperators.remove(0);
                    startedChaining = false;
                    manageStack(stack);
                } else {
                    stackTmp.add(stack.remove(indiceFirstArg));
                    manageStack(stackTmp);
                }
                write(",\'" + stack.remove(indiceFirstArg).toString() + "\')");
                break;
            case plus:
                isTemporalPredicate = true;
                indiceFirstArg--;
                if (!startedChaining) {
                    startedChaining = true;
                    stackTmp.add(stack.remove(indiceFirstArg));
                    manageStack(stackTmp);
                }
                write(".add(");
                decreaseCount(countDateOperators);
                boolean finished = false;
                if (countDateOperators.get(0) == 0) {
                    countDateOperators.remove(0);
                    startedChaining = false;
                    finished = true;
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                } else {
                    stackTmp.add(stack.remove(indiceFirstArg));
                    manageStack(stackTmp);
                }
                write(",\'" + stack.remove(indiceFirstArg).toString() + "\')");
                break;
            case after:
                isTemporalPredicate = true;
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".isAfter(");
                decreaseCount(countDateOperators);
                if (countDateOperators.get(0) == 0) {
                    countDateOperators.remove(0);
                    startedChaining = false;
                    manageStack(stack);
                } else {
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                }
                parentheseDepth++;
                break;
            case after_or_equals:
                isTemporalPredicate = true;
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".isSameOrAfter(");
                decreaseCount(countDateOperators);
                if (countDateOperators.get(0) == 0) {
                    countDateOperators.remove(0);
                    startedChaining = false;
                    manageStack(stack);
                } else {
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                }
                parentheseDepth++;
                break;
            case age_at:
                isTemporalPredicate = true;
                indiceFirstArg--;
                if (!startedChaining) {
                    write("Math.round(Math.abs(");               // using Math.round(...)
                    stackTmp.add(stack.remove(0));                        // ex : diff(31may,31may + 1month) = 0.96
                    manageStack(stackTmp);
                }
                write(".diff(");                                   //Math.abs so the date order doesn't matter
                decreaseCount(countDateOperators);
                if (countDateOperators.get(0) == 0) {
                    countDateOperators.remove(0);
                    startedChaining = false;
                    manageStack(stack);
                }else{
                stackTmp.add(stack.remove(indiceFirstArg));
                manageStack(stackTmp);
        }
                write(", \'years\')))");
                isTemporalPredicate = false;
                break;
            case before:
                isTemporalPredicate = true;
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".isBefore(" );
                decreaseCount(countDateOperators);
                if(countDateOperators.get(0)==0){
                    countDateOperators.remove(0);
                    startedChaining = false;
                    manageStack(stack);
                } else {
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                }
                parentheseDepth++;
                break;
            case before_or_equals:
                isTemporalPredicate = true;
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".isSameOrBefore(" );
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                parentheseDepth++;
                break;
            case matches:
                write(".match(/");
                parentheseDepth++;
                useRegexp = true;
                isMatch = true;
                break;
            case and:
                write(" && ");
                break;
            case or:
                write(" || ");
                break;
            case contains:
                if (isSiblingIterable(element, false)) {
                    write(".every(function(element){ return ");
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                    write(".some(function(elt){ return elt.match(element);});})");
                } else {
                    write(".some(function(element){ return element.match(/");
                    isMatch = true;
                    useRegexp = true;
                    stackTmp.add(stack.remove(0));
                    manageStack(stackTmp);
                    write(");})");
                }
                break;
            case starts_with:
                write(".match(/^");
                startWithCount = true;
                parentheseDepth++;
                useRegexp = true;
                break;
            case ends_with:
                write(".match(/.*");
                endWithCount = true;
                parentheseDepth++;
                useRegexp = true;
                break;
            case greater_than:
                write(" > ");
                if (stack != null && stack.size() > 0) {
                    write(stack.remove(0).toString());
                }
                break;
            case greater_or_equals:
                write(" >= ");
                if (stack != null && stack.size() > 0) {
                    write(stack.remove(0).toString());
                }
                break;
            case is:
                write(" === ");
                break;
            case lesser_than:
                write(" < ");
                if (stack != null && stack.size() > 0) {
                    write(stack.remove(0).toString());
                }
                break;
            case lesser_or_equals:
                write(" <= ");
                if (stack != null && stack.size() > 0) {
                    write(stack.remove(0).toString());
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
                write("moment(moment().format(\"YYYY-MM-DD\")).startOf('month')");
                break;
            case first_day_of_this_year:
                write("moment(moment().format(\"YYYY-MM-DD\")).startOf('year')");
                break;
            case last_day_of_this_month:
                write("moment(moment().format(\"YYYY-MM-DD\")).endOf('month')");
                break;
            case last_day_of_this_year:
                write("moment(moment().format(\"YYYY-MM-DD\")).endOf('year')");
                break;
            case first_day_of_month:
                isTemporalPredicate = true;
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").startOf('month')");
                break;
            case first_day_of_next_month:
                write("moment(moment().format(\"YYYY-MM-DD\")).add(1,'month').startOf('month')");
                break;
            case first_day_of_year:
                isTemporalPredicate = true;
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").startOf('year')");
                break;
            case first_day_of_next_year:
                write("moment(moment().format(\"YYYY-MM-DD\")).add(1,'year').startOf('year')");
                break;
            case last_day_of_month:
                isTemporalPredicate = true;
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").endOf('month')");
                break;
            case last_day_of_year:
                isTemporalPredicate = true;
                write("moment(");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(").endOf('year')");
                break;
            case match_all:
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".every(function(element){ return ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                if (isMatch) {
                    write(".every(function(elt){ return elt.match(element);});\n})");
                }
                break;
            case match_none:
                write(".every(function(element){ return ");
                stackTmp.add(stack.remove(0));
                manageStack(stackTmp);
                write(".indexOf(element) < 0;})");
                break;
            case match_any:
                break;
            case count:
                break;
            case sum:
                break;
            case min:
                break;
            case when:
                break;
            case xor:
                manageXOR(stack.remove(0), stack.remove(0));
                break;
        }

    }

    public void decreaseCount(ArrayList<Integer> list){
        if(list.size()>0){
            list.set(0,list.get(0) - 1);
        }
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
                    startedChaining = false;
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
        write("(!" + leftMD + " && " + rightMD + ") " +
                "|| (" + leftMD + " && !" + rightMD + ")");
    }

    private void manageXOR(Element leftMD, Element rightMD) {
        write("(!" + leftMD.toString() + " && " + rightMD.toString() + ") " +
                "|| (" + leftMD.toString() + " && !" + rightMD.toString() + ")");
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
        indiceFirstArg = -1;
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

    public String manageTabValues(String values) {
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

        return values;
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

    protected void write(String str) {
        try {
            ops.write(str.getBytes(StandardCharsets.UTF_8));
        } catch (IOException ioe) {
            throw new RuntimeException(ioe);
        }
    }
}
