/*
 * Copyright (C) by Courtanet, All Rights Reserved.
 */
package io.doov.js.ast;

import static io.doov.core.dsl.meta.DefaultOperator.*;
import static io.doov.core.dsl.meta.ElementType.OPERATOR;
import static org.apache.commons.lang3.StringUtils.isNumeric;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.lang3.StringUtils;

import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.*;

public class AstJavascriptWriter {

    protected final OutputStream ops;
    protected ValidationRule rule;
    private String output;

    private int parenthesisCount; // compte le nombre de parenthèse à rajouter avant de fermer le 'if'
    private int anyAllNoneContains; //0 : match_any; 1 : match_all; 2 : match_none; 3 : contains
    private boolean isStartsWith;  // permet de dire si on est dans l'opérateur starts_with
    private boolean isEndsWith; // permet de dire si on est dans l'opérateur ends_with
    private boolean isMatch;    // permet de dire si on est dans un opérateur de matches
    private boolean useRegexp;  // permet de dire si on utilise une regexp
    private boolean isTemporalPredicate;    // permet de dire si on est dans un opérateur temporel
    private boolean alreadyComputed;    // permet de dire si des valeurs on déja été écrite (operateur temporel)
    private boolean isDiff; // permet de dire si on est dans l'opérateur age_at
    private boolean isBeforeOrAfter;    // permet de dire si on est dans l'opérateur before, before_or_same, after, ...

    public AstJavascriptWriter(OutputStream ops) {
        this.ops = ops;
        this.output = "";
    }

    public void initValue() {
        this.parenthesisCount = 0;
        this.anyAllNoneContains = -1;
        this.isMatch = false;
        this.isEndsWith = false;
        this.isStartsWith = false;
        this.useRegexp = false;
        this.isTemporalPredicate = false;
        this.alreadyComputed = false;
        this.isBeforeOrAfter = false;
        this.isDiff = false;
    }

    public void writeRule(ValidationRule rule) {
        initValue();
        this.rule = rule;
        Metadata ruleMetadata = rule.metadata().children().findFirst().get();
        Metadata whenMetadata = ruleMetadata.children().findFirst().get();
        output = writeMetadata(whenMetadata);
        while (parenthesisCount > 0) {
            parenthesisCount--;
            output += ")";
        }
        output = "if(" + output + "){ true; } else { false; }";
        write(output);
        output = "";
    }

    private String writeMetadata(Metadata metadata) {
        String[] returnValue = new String[1];
        returnValue[0] = "";
        switch (metadata.type()) {
            case BINARY_PREDICATE:
                returnValue[0] += writeBinary(metadata);
                break;
            case LEAF_PREDICATE:
            case FIELD_PREDICATE:
                if (metadata.flatten().size() == 2 && metadata.flatten().get(1).getReadable() == not) {
                    returnValue[0] += "!(" + writeElement(metadata.flatten().get(0), "") + ")"; // eval_not_false/true
                } else if (metadata.flatten().size() == 3 && metadata.flatten().get(1).getReadable() == xor) {
                    returnValue[0] += writeXOR(metadata.flatten().get(0), metadata.flatten().get(2)); // eval_XOR_*
                } else {
                    metadata.flatten().forEach(elt -> {
                        boolean matched = false;
                        if (elt.getType() == OPERATOR) {
                            DefaultOperator operator = (DefaultOperator) elt.getReadable();
                            if (operator == match_none || operator == match_all
                                    || operator == match_any || operator == contains
                                    || operator == starts_with || operator == ends_with
                                    || operator == after || operator == after_or_equals
                                    || operator == before || operator == before_or_equals
                                    || operator == age_at || operator == equals) {
                                returnValue[0] = writeElement(elt, returnValue[0]);
                                matched = true;
                            }
                        }
                        if (!matched) {
                            returnValue[0] += writeElement(elt, "");
                        }
                    });
                }
                break;
            case FIELD_PREDICATE_MATCH_ANY:
                metadata.flatten().forEach(elt -> {
                    boolean matched = false;
                    if (elt.getType() == OPERATOR) {
                        DefaultOperator operator = (DefaultOperator) elt.getReadable();
                        if (operator == match_none || operator == match_all || operator == match_any) {
                            returnValue[0] = writeElement(elt, returnValue[0]);
                            matched = true;
                        }
                    }
                    if (!matched) {
                        returnValue[0] += writeElement(elt, "");
                    }
                });
                break;
            case NARY_PREDICATE:
                returnValue[0] += writeNary(metadata);
                break;
            case UNARY_PREDICATE:
                returnValue[0] += writeUnary(metadata);
                break;
            case EMPTY:
                break;
            case SINGLE_MAPPING:
                break;
            case MULTIPLE_MAPPING:
                break;
            case THEN_MAPPING:
                break;
            case ELSE_MAPPING:
                break;
            case MAPPING_INPUT:
                break;
            case MAPPING_LEAF:
                break;
            case TYPE_CONVERTER:
                break;
            case TYPE_CONVERTER_IDENTITY:
                break;
        }
        return returnValue[0];
    }

    private String writeElement(Element element, String returnValue) {
        switch (element.getType()) {
            case FIELD:
                returnValue = writeField(element, returnValue);
                break;
            case OPERATOR:
                returnValue = writeOperator(element, returnValue);
                break;
            case VALUE:
            case STRING_VALUE:
                returnValue += writeValue(element, returnValue);
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
        return returnValue;
    }

    private String writeNary(Metadata metadata) {
        String[] returnValue = new String[1];
        returnValue[0] = "";
        NaryMetadata naryMetadata = (NaryMetadata) metadata;
        DefaultOperator operator =
                (DefaultOperator) naryMetadata.getOperator();
        switch (operator) {
            case min:
                returnValue[0] += "Math.min.apply(null,[";
                break;
            case match_none:
                returnValue[0] += "!";
                break;
            case count:
            case sum:
                returnValue[0] += "[";
                break;
        }
        naryMetadata.children().forEach(elt ->
        {
            returnValue[0] += writeMetadata(elt);
            if (!elt.equals(naryMetadata.children().skip(naryMetadata.children().count() - 1).findFirst().get())) {
                switch (operator) {
                    case match_any:
                        returnValue[0] += " || ";                       // using 'or' operator to match any of the
                        // predicate given
                        break;
                    case match_all:
                        returnValue[0] += " && ";                       // using 'and' operator for match all
                        break;
                    case match_none:
                        returnValue[0] += " && !";                      // 'and not' for match none
                        break;
                    case min:
                    case sum:
                    case count:
                        returnValue[0] += ", ";                         // separating the list values
                        break;
                }
            }
        });
        switch (operator) {
            case count:
                returnValue[0] += "].reduce(function(acc,val){ return val ? acc + 1 : acc},0)";
                break;
            case min:
                returnValue[0] += "])";
                break;
            case sum:
                returnValue[0] += "].reduce(function(acc,val){ return acc+val;},0)";
                break;
        }
        return returnValue[0];
    }

    private String writeBinary(Metadata metadata) {
        String returnValue = "";
        BinaryMetadata binaryMetadata = (BinaryMetadata) metadata;
        Element operator = metadata.flatten().get(binaryMetadata.getLeft().flatten().size());
        returnValue += "(";
        if ((DefaultOperator) operator.getReadable() == xor) {
            writeXOR(binaryMetadata.getLeft(), binaryMetadata.getRight());
        } else {
            returnValue += writeMetadata(binaryMetadata.getLeft());
            returnValue += writeOperator(operator, "");
            returnValue += writeMetadata(binaryMetadata.getRight());
        }
        returnValue += ")";
        return returnValue;
    }

    private String writeLeaf(Metadata metadata, String returnValue) {
        String[] values = new String[1];
        values[0] = returnValue;
        metadata.flatten().forEach(elt -> {
            values[0] = writeElement(elt, returnValue);
        });
        return values[0];
    }

    private String writeOperator(Element element, String returnValue) {
        DefaultOperator operator = (DefaultOperator) element.getReadable();
        List<Element> flatList;
        String numValue;
        String tempValue;
        switch (operator) {
            case and:
                returnValue += " && ";
                break;
            case or:
                returnValue += " || ";
                break;
            case match_any:
                anyAllNoneContains = 0;
                isMatch = true;
                return isSiblingIterable(element, true) ? returnValue + ".some(function(element){ return "
                        : "[" + returnValue + "].some(function(element){ return ";
            case match_all:
                anyAllNoneContains = 1;
                isMatch = true;
                return isSiblingIterable(element, true) ? returnValue + ".every(function(element){ return "
                        : "[" + returnValue + "].every(function(element){ return ";
            case match_none:
                anyAllNoneContains = 2;
                isMatch = true;
                return isSiblingIterable(element, true) ? returnValue + ".every(function(element){ return "
                        : "[" + returnValue + "].every(function(element){ return ";
            case count:
                break;
            case sum:
                break;
            case min:
                break;
            case not:
                returnValue += "!(" + returnValue + ")";
                break;
            case always_true:
                returnValue += " true ";
                break;
            case always_false:
                returnValue += " false ";
                break;
            case times:
                returnValue += " * ";
                break;
            case when:
                break;
            case equals:
                flatList = rule.metadata().flatten();
                if (isDiff) {
                    returnValue = returnValue + ",\'years\')))";
                }
                int indexElement = flatList.indexOf(element) - 1;
                if ((indexElement - 1 >= 0 && flatList.get(flatList.indexOf(element) - 1).getReadable().toString().contains("LocalDate"))
                        || isTemporalPredicate && !isDiff) {
                    parenthesisCount++;
                    isTemporalPredicate = true;
                    alreadyComputed = false; //eval_plus_value
                    return "moment(" + returnValue + ").isSame(";
                } else {
                    isDiff = false;
                    isTemporalPredicate = false;
                    alreadyComputed = false; //reduce_doc_years_between
                    return returnValue + " == ";
                }
            case not_equals:
                returnValue += " != ";
                break;
            case is_null:
                returnValue += " === (null || undefined || \"\")";
                break;
            case is_not_null:
                returnValue += " !== (null && undefined && \"\")";
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
                isTemporalPredicate = true;
                alreadyComputed = true;
                flatList = rule.metadata().flatten();
                numValue = flatList.get(flatList.indexOf(element) + 1).toString();
                if (!isNumeric(numValue)) {
                    numValue = "moment(" + numValue + ")"; // eval_minus*
                }
                tempValue = flatList.get(flatList.indexOf(element) + 2).toString();
                if (isBeforeOrAfter) {
                    isBeforeOrAfter = false;
                    parenthesisCount--;
                    returnValue += ")";
                }
                return returnValue + ".subtract(" + numValue + ",\'" + tempValue + "\')";
            case plus:
                isTemporalPredicate = true;
                alreadyComputed = true;
                flatList = rule.metadata().flatten();
                numValue = flatList.get(flatList.indexOf(element) + 1).toString();
                if (!isNumeric(numValue)) {
                    numValue = "moment(" + numValue + ")"; // eval_plus
                }
                tempValue = flatList.get(flatList.indexOf(element) + 2).toString();
                if (isBeforeOrAfter) {
                    isBeforeOrAfter = false;
                    parenthesisCount--;
                    returnValue += ")";
                }
                return returnValue + ".add(" + numValue + ",\'" + tempValue + "\')";
            case after:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                isBeforeOrAfter = true;
                return "moment(" + returnValue + ").isAfter(moment(";
            case after_or_equals:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                isBeforeOrAfter = true;
                return "moment(" + returnValue + ").isSameOrAfter(moment(";
            case age_at:
                isTemporalPredicate = true;
                isDiff = true;
                return "Math.round(Math.abs(moment(" + returnValue + ").diff(";
            case before:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                isBeforeOrAfter = true;
                return "moment(" + returnValue + ").isBefore(moment(";
            case before_or_equals:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                isBeforeOrAfter = true;
                return "moment(" + returnValue + ").isSameOrBefore(moment(";
            case matches:
                isMatch = true;
                useRegexp = true;
                return returnValue + ".match(/";
            case contains:
                anyAllNoneContains = 3;
                String containString;
                if (isSiblingIterable(element, true)) {
                    if (isSiblingIterable(element, false)) {
                        anyAllNoneContains = 1;
                        containString = returnValue + ".every(function(element){ return ";
                    } else {
                        anyAllNoneContains = 3;
                        containString = returnValue + ".some(function(element){return element.match(";
                    }
                } else {
                    anyAllNoneContains = 3;
                    isStartsWith = true;
                    useRegexp = true;
                    isMatch = true;
                    containString = "[" + returnValue + "].some(function(element){return element.match(/.*";
                }
                return containString;
            case starts_with:
                isStartsWith = true;
                useRegexp = true;
                isMatch = true;
                String[] tabString = returnValue.split(" ");
                String argString = tabString[tabString.length - 1];
                return returnValue.replace(argString, "") + "[" + argString + "].some(function(element){ return " +
                        "element.match(/^";
            case ends_with:
                isEndsWith = true;
                useRegexp = true;
                isMatch = true;
                return "[" + returnValue + "].some(function(element){ return element.match(/.*";
            case greater_than:
                returnValue += " > ";
                break;
            case greater_or_equals:
                returnValue += " >= ";
                break;
            case is:
                returnValue += " === ";
                break;
            case lesser_than:
                returnValue += " < ";
                break;
            case lesser_or_equals:
                returnValue += " <= ";
                break;
            case has_not_size:
                returnValue += ".length != ";
                break;
            case has_size:
                returnValue += ".length == ";
                break;
            case is_empty:
                returnValue += ".length == 0";
                break;
            case is_not_empty:
                returnValue += ".length != 0";
                break;
            case length_is:
                returnValue += ".length ";
                break;
            case today:
                returnValue += "moment(moment().format(\"YYYY-MM-DD\"))";
                break;
            case today_plus:
                parenthesisCount++;
                returnValue += "moment(moment().format(\"YYYY-MM-DD\")).add(";
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
        return returnValue;
    }

    private String writeUnary(Metadata metadata) {
        String[] returnValue = new String[1];
        returnValue[0] = "";
        UnaryMetadata unaryMetadata = (UnaryMetadata) metadata;
        DefaultOperator operator = (DefaultOperator) unaryMetadata.getOperator();
        switch (operator) {
            case not:                                                       // eval_not_second_false
                returnValue[0] += "!(";
                unaryMetadata.children().forEach(elt -> {
                    returnValue[0] += writeMetadata(elt);
                });
                returnValue[0] += ")";
                break;
        }
        return returnValue[0];
    }

    private String writeValue(Element element, String returnValue) {
        if (!alreadyComputed) {
            if (element.getType() == ElementType.STRING_VALUE) {
                if (isTemporalPredicate) {
                    returnValue = "moment(\'" + element.toString() + "\')";
                } else if (useRegexp) {
                    useRegexp = false;
                    if (isMatch) {
                        isMatch = false;
                        if (isStartsWith) {
                            isStartsWith = false;
                            returnValue = returnValue + formatRegexp(element.toString()) + ".*/);})";
                        } else if (isEndsWith) {
                            isEndsWith = false;
                            returnValue = returnValue + formatRegexp(element.toString()) + "$/);})";
                        } else {
                            returnValue = returnValue + element.toString() + "/)";
                        }
                    } else {
                        returnValue = returnValue + formatRegexp(element.toString());
                    }
                } else {
                    if (useRegexp) {
                        useRegexp = false;
                        returnValue = returnValue + "\'" + element.toString() + "\'.*/);})";
                    } else {
                        if (anyAllNoneContains != -1) {
                            returnValue = returnValue + "\'" + element.toString() + "\');})";
                        } else {
                            returnValue = returnValue + "\'" + element.toString() + "\'";
                        }
                    }

                }
            } else {
                if (element.toString().startsWith(" : ")) {
                    returnValue += writeTabValues(element.toString().replace(" : ", ""));
                } else if (StringUtils.isNumeric(element.toString())) {
                    returnValue = returnValue + element.toString();
                } else {
                    if (isTemporalPredicate) {
                        isTemporalPredicate = false;
                        if (element.getReadable().toString().contains("DateField")) {
                            returnValue = returnValue + "moment(" + element.toString() + ")";
                        } else {
                            returnValue = returnValue + "moment(\'" + element.toString() + "\')";
                        }
                    } else {
                        returnValue = returnValue + element.toString();
                    }
                }
            }
        } else {
            alreadyComputed = false;
        }
        return returnValue;
    }

    private String writeField(Element element, String returnValue) {
        if (alreadyComputed) {
            alreadyComputed = false;
            return returnValue;
        } else {
            if (element.getReadable().toString().contains("Date")) {
                return returnValue + "moment(" + element.toString() + ")";
            } else if (isTemporalPredicate) {
                isTemporalPredicate = false;
                if (isDiff) {
                    return returnValue + "moment(" + element.toString() + ")";
                }

            }
            return returnValue + element.toString();
        }
    }

    private String writeXOR(Metadata left, Metadata right) {
        return "(!" + writeMetadata(left) + " && " + writeMetadata(right) + ") " +
                "|| (" + writeMetadata(left) + " && !" + writeMetadata(right) + ")";
    }

    private String writeXOR(Element left, Element right) {
        return "(!" + left.toString() + " && " + right.toString() + ") " +
                "|| (" + left.toString() + " && !" + right.toString() + ")";
    }

    public String writeTabValues(String values) {
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
        switch (anyAllNoneContains) {
            case 0:
                values += ".indexOf(element) >= 0 ;})";
                isMatch = false;
                break;
            case 1:
                if (isMatch) {
                    values += ".every(function(elt){ return elt.match(element);});})";
                } else {
                    values += ".some(function(elt){ return elt.match(element);});})";
                }
                isMatch = false;
                break;
            case 2:
                values += ".indexOf(element) < 0;})";
                isMatch = false;
                break;
            case 3:
                if (useRegexp) {
                    values += ".*/);})";
                    useRegexp = false;
                } else {
                    values += ");})";
                }
            default:
                break;
        }
        anyAllNoneContains = -1;
        return values;
    }

    /**
     * let us know if the element directly before or after the called element is an iterable
     *
     * @param element the element around which we search the iterable
     * @param before  true : before; false : after
     * @return true if the sibling before/after the element is an iterable
     */
    private boolean isSiblingIterable(Element element, boolean before) {
        ArrayList<Element> flatData = (ArrayList<Element>) rule.metadata().flatten();
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
