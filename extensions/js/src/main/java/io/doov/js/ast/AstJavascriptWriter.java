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
import java.util.Deque;

import org.apache.commons.lang3.StringUtils;

import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.*;

public class AstJavascriptWriter {

    protected final OutputStream ops;
    protected ValidationRule rule;
    private String output;

    private int parenthesisCount; // keep a count of the parenthesis to close before the final 'if'
    private int anyAllNoneContains; // 0 : match_any | 1 : match_all | 2 : match_none | 3 : contains
    private boolean isStartsWith;  // allow us to know if we are in the operator starts_with
    private boolean isEndsWith; // allow us to know if we are in the operator ends_with
    private boolean isMatch;    // allow us to know if we are in a 'matches' operator
    private boolean useRegexp;  // allow us to know if we use a regular expression
    private boolean isTemporalPredicate;    // allow us to know if we are in a temporal operator
    private boolean alreadyComputed;    // allow us to know if some value have already been processed
    private boolean isFinished; // keep track if we finished processing the elements remaining (NaryMetadata)
    private boolean isDiff; // allow us to know if we are in the operator age_at
    private static ArrayList<DefaultOperator> exceptionOperator;

    public AstJavascriptWriter(OutputStream ops) {
        this.ops = ops;
        this.output = "";
        exceptionOperator = new ArrayList<>();
        initExceptionOperator();
    }

    private void initExceptionOperator() {
        exceptionOperator.add(match_none);
        exceptionOperator.add(match_all);
        exceptionOperator.add(match_any);
        exceptionOperator.add(contains);
        exceptionOperator.add(starts_with);
        exceptionOperator.add(ends_with);
        exceptionOperator.add(after);
        exceptionOperator.add(after_or_equals);
        exceptionOperator.add(before);
        exceptionOperator.add(before_or_equals);
        exceptionOperator.add(age_at_days);
        exceptionOperator.add(age_at_months);
        exceptionOperator.add(age_at_years);
        exceptionOperator.add(equals);
        exceptionOperator.add(greater_or_equals);
        exceptionOperator.add(greater_than);
        exceptionOperator.add(lesser_than);
        exceptionOperator.add(lesser_or_equals);
        exceptionOperator.add(as_a_number);
        exceptionOperator.add(as_string);
    }

    private void initValue() {
        this.parenthesisCount = 0;
        this.anyAllNoneContains = -1;
        this.isMatch = false;
        this.isEndsWith = false;
        this.isStartsWith = false;
        this.useRegexp = false;
        this.isTemporalPredicate = false;
        this.alreadyComputed = false;
        this.isDiff = false;
        this.isFinished = false;
    }

    public void writeRule(ValidationRule rule) {
        initValue();
        this.rule = rule;
        Metadata whenMetadata = rule.getStepWhen().stepCondition().metadata();
        if (null != whenMetadata) {
            output = writeMetadata(whenMetadata);
            while (parenthesisCount > 0) {
                parenthesisCount--;
                output += ")";
            }
            output = "if(" + writeForDiff(output) + "){ true; } else { false; }";
            write(output);
            output = "";
        } else {
            throw new RuntimeException("No children were found for the ValidationRule");
        }
    }

    private String writeMetadata(Metadata metadata) {
        if (alreadyComputed) {
            alreadyComputed = false;
            return "";
        }
        String[] returnValue = new String[1];
        returnValue[0] = "";
        switch (metadata.type()) {
            case RULE:
                break;
            case WHEN:
                break;
            case LEAF_VALUE:
                ((LeafMetadata) metadata).elementsAsList().forEach(elt ->
                        returnValue[0] += writeElement((Element) elt, returnValue[0], metadata));
                break;
            case BINARY_PREDICATE:
                returnValue[0] += writeBinary(metadata);
                break;
            case LEAF_PREDICATE: // Same processing as FIELD_PREDICATE
            case FIELD_PREDICATE:
                LeafMetadata metaLeaf = (LeafMetadata) metadata;
                if (metaLeaf.elementsAsList().size() == 2 && metaLeaf.elementsAsList().get(1) == not) {
                    // test eval_not_false/true out of a leaf metadata
                    returnValue[0] += "!(" + writeElement((Element) metaLeaf.elementsAsList().get(0), "", metaLeaf) + ")";
                } else if (metaLeaf.elementsAsList().size() == 3 && ((Element) metaLeaf.elementsAsList().get(1)).getReadable() == xor) {
                    // test eval_XOR_* special case
                    returnValue[0] += writeXOR(((Element) metaLeaf.elementsAsList().get(0)),
                            ((Element) metaLeaf.elementsAsList().get(2)));
                } else {
                    metaLeaf.elementsAsList().forEach(elt -> {
                        boolean matched = false;
                        if (((Element) elt).getType() == OPERATOR) {
                            DefaultOperator operator = (DefaultOperator) ((Element) elt).getReadable();
                            if (exceptionOperator.contains(operator)) {
                                returnValue[0] = writeElement((Element) elt, returnValue[0], metaLeaf);
                                matched = true;
                            }
                        }
                        if (!matched) {
                            returnValue[0] += writeElement(((Element) elt), "", metaLeaf);
                        }

                    });
                }
                break;
            case FIELD_PREDICATE_MATCH_ANY:
                LeafMetadata metaLeafTmp = ((LeafMetadata) metadata);
                metaLeafTmp.elementsAsList().forEach(elt -> {
                    boolean matched = false;
                    if (((Element) elt).getType() == OPERATOR) {
                        DefaultOperator operator = (DefaultOperator) ((Element) elt).getReadable();
                        if (operator == match_none || operator == match_all || operator == match_any) {
                            returnValue[0] = writeElement(((Element) elt), returnValue[0], metaLeafTmp);
                            matched = true;
                        }
                    }
                    if (!matched) {
                        returnValue[0] += writeElement(((Element) elt), "", metaLeafTmp);
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
                returnValue[0] += "/*EMPTY*/";
                break;
            case SINGLE_MAPPING:
                returnValue[0] += "/*SINGLE_MAPPING*/";
                break;
            case MULTIPLE_MAPPING:
                returnValue[0] += "/*MULTIPLE_MAPPING*/";
                break;
            case THEN_MAPPING:
                returnValue[0] += "/*THEN_MAPPING*/";
                break;
            case ELSE_MAPPING:
                returnValue[0] += "/*ELSE_MAPPING*/";
                break;
            case MAPPING_INPUT:
                returnValue[0] += "/*MAPPING_INPUT*/";
                break;
            case MAPPING_LEAF:
                returnValue[0] += "/*MAPPING_LEAF*/";
                break;
            case TYPE_CONVERTER:
                returnValue[0] += "/*TYPE_CONVERTER*/";
                break;
            case TYPE_CONVERTER_IDENTITY:
                returnValue[0] += "/*TYPE_CONVERTER_IDENTITY*/";
                break;

            default:
                break;
        }
        return returnValue[0];
    }

    private String writeElement(Element element, String returnValue, Metadata metadata) {
        if (!isFinished) {
            switch (element.getType()) {
                case FIELD:
                    returnValue = writeField(element, returnValue);
                    break;
                case OPERATOR:
                    returnValue = writeOperator((DefaultOperator) element.getReadable(), returnValue, metadata);
                    break;
                case VALUE:
                case STRING_VALUE:
                    returnValue = writeValue(element, returnValue, metadata);
                    isMatch = false;
                    break;
                case PARENTHESIS_LEFT:
                    returnValue += "/*PARENTHESIS_LEFT*/";
                    break;
                case PARENTHESIS_RIGHT:
                    returnValue += "/*PARENTHESIS_RIGHT*/";
                    break;
                case TEMPORAL_UNIT:
                    returnValue += "\'" + element.toString() + "\'";
                    break;
                case UNKNOWN:
                    returnValue += "/*UNKNOWN*/";
                    break;
            }
        }
        return returnValue;
    }

    private String writeNary(Metadata metadata) {
        String[] returnValue = new String[1];
        returnValue[0] = "";
        NaryMetadata naryMetadata = (NaryMetadata) metadata;
        DefaultOperator operator =
                (DefaultOperator) naryMetadata.getOperator();

        returnValue[0] = startNary(operator);

        if (naryMetadata.children().findAny().isPresent()) {
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
        } else {
            throw new RuntimeException("No children were found for the Nary-Metadata");
        }

        returnValue[0] += endNary(operator);

        return returnValue[0];
    }

    private String startNary(DefaultOperator operator) {
        switch (operator) {
            case min:
                return "Math.min.apply(null,[";
            case match_none:
                return "!";
            case count:
            case sum:
                return "[";
        }
        return "";
    }

    private String endNary(DefaultOperator operator) {
        switch (operator) {
            case count:
                return "].reduce(function(acc,val){ return val ? acc + 1 : acc},0)";
            case min:
                return "])";
            case sum:
                return "].reduce(function(acc,val){ return acc+val;},0)";
        }
        return "";
    }

    private String writeBinary(Metadata metadata) {
        String returnValue = "";
        BinaryMetadata binaryMetadata = (BinaryMetadata) metadata;
        DefaultOperator operator = (DefaultOperator) metadata.getOperator();
        if (operator == xor) {
            returnValue += writeXOR(binaryMetadata.getLeft(), binaryMetadata.getRight());
        } else {
            returnValue += writeMetadata(binaryMetadata.getLeft());
            returnValue = writeOperator(operator, returnValue, binaryMetadata);
            returnValue += writeMetadata(binaryMetadata.getRight());
        }
        return returnValue;
    }

    private String writeOperator(DefaultOperator element, String returnValue, Metadata metadata) {
        if (isFinished) {
            return "";
        }
        Deque<Element> deque;
        String tmpTodayValue;
        String[] returnValueTab = new String[1];
        returnValueTab[0] = returnValue;
        switch (element) {
            case no_operator:
                break;
            case rule:
                break;
            case validate:
                break;
            case empty:
                break;
            case and:
                returnValueTab[0] += " && ";
                break;
            case or:
                returnValueTab[0] += " || ";
                break;
            case match_any:
                anyAllNoneContains = 0;
                isMatch = true;
                return isIterableOrField(metadata.left().findFirst().get()) ? returnValueTab[0] + ".some(function" +
                        "(element){ " +
                        "return "
                        : "[" + returnValueTab[0] + "].some(function(element){ return ";
            case match_all:
                anyAllNoneContains = 1;
                isMatch = true;
                return isIterableOrField(metadata.left().findFirst().get()) ? returnValueTab[0] + ".every(function" +
                        "(element){" +
                        " return "
                        : "[" + returnValueTab[0] + "].every(function(element){ return ";
            case match_none:
                anyAllNoneContains = 2;
                isMatch = true;
                return isIterableOrField(metadata.left().findFirst().get()) ? returnValueTab[0] + ".every(function" +
                        "(element){" +
                        " return "
                        : "[" + returnValueTab[0] + "].every(function(element){ return ";
            case any_match_values:
                anyAllNoneContains = 0;
                isMatch = true;
                return isIterableOrField(metadata.left().findFirst().get()) ? returnValueTab[0] + ".some(function" +
                        "(element){ " +
                        "return "
                        : "[" + returnValueTab[0] + "].some(function(element){ return ";
            case all_match_values:
                anyAllNoneContains = 1;
                isMatch = true;
                return isIterableOrField(metadata.left().findFirst().get()) ? returnValueTab[0] + ".every(function" +
                        "(element){" +
                        " return "
                        : "[" + returnValueTab[0] + "].every(function(element){ return ";
            case none_match_values:
                anyAllNoneContains = 2;
                isMatch = true;
                return isIterableOrField(metadata.left().findFirst().get()) ? returnValueTab[0] + ".every(function" +
                        "(element){" +
                        " return "
                        : "[" + returnValueTab[0] + "].every(function(element){ return ";
            case count:
                break;
            case sum:
                break;
            case min:
                break;
            case not:
                returnValueTab[0] += "!(" + returnValueTab[0] + ")";
                break;
            case always_true:
                returnValueTab[0] += " true ";
                break;
            case always_false:
                returnValueTab[0] += " false ";
                break;
            case times:
                returnValueTab[0] += " * ";
                break;
            case when:
                break;
            case equals:
                if (isTemporalPredicate) {
                    returnValueTab[0] += ".isSame(";
                    parenthesisCount++;
                } else {
                    returnValueTab[0] += " === ";
                }
                break;
            case not_equals:
                returnValueTab[0] += " != ";
                break;
            case is_null:
                returnValueTab[0] += " === (null || undefined || \"\")";
                break;
            case is_not_null:
                returnValueTab[0] += " !== (null && undefined && \"\")";
                break;
            case as_a_number:
                returnValueTab[0] = "Number(" + returnValueTab[0] + ")";
                break;
            case as_string:
                returnValueTab[0] = "String(" + returnValueTab[0] + ")";
                break;
            case as:
                break;
            case with:
                break;
            case minus:
                isTemporalPredicate = true;
                returnValueTab[0] += ".subtract(";
                deque = ((LeafMetadata) metadata.right().findFirst().get()).elements();
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata) + ", ";
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata);
                alreadyComputed = true;
                return returnValueTab[0] + ")";
            case plus:
                isTemporalPredicate = true;
                returnValueTab[0] += ".add(";
                deque = ((LeafMetadata) metadata.right().findFirst().get()).elements();
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata) + ", ";
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata);
                alreadyComputed = true;
                return returnValueTab[0] + ")";
            case after:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                return "moment(" + returnValueTab[0] + ").isAfter(moment(";
            case after_or_equals:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                return "moment(" + returnValueTab[0] + ").isSameOrAfter(moment(";
            case age_at_days:
                isTemporalPredicate = true;
                isDiff = true;
                returnValueTab[0] += ".diff(";
                deque = ((LeafMetadata) metadata.right().findFirst().get()).elements();
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata) + ", \'days\')";
                returnValueTab[0] = writeForDiff(returnValueTab[0]);
                isTemporalPredicate = false;
                return returnValueTab[0];
            case age_at_months:
                isTemporalPredicate = true;
                isDiff = true;
                returnValueTab[0] += ".diff(";
                deque = ((LeafMetadata) metadata.right().findFirst().get()).elements();
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata) + ", \'months\')";
                returnValueTab[0] = writeForDiff(returnValueTab[0]);
                isTemporalPredicate = false;
                return returnValueTab[0];
            case age_at_years:
                isTemporalPredicate = true;
                isDiff = true;
                returnValueTab[0] += ".diff(";
                Metadata metaTemp = metadata.right().findFirst().get();
                if (metaTemp.getClass().toString().contains("TemporalBiFunction")) {
                    returnValueTab[0] += writeMetadata(metaTemp);
                    alreadyComputed = true;
                } else {
                    deque = ((LeafMetadata) metaTemp).elements();
                    returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata);
                }
                returnValueTab[0] = writeForDiff(returnValueTab[0] + ", \'years\')");
                isTemporalPredicate = false;
                return returnValueTab[0];
            case before:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                return "moment(" + returnValueTab[0] + ").isBefore(moment(";
            case before_or_equals:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                return "moment(" + returnValueTab[0] + ").isSameOrBefore(moment(";
            case matches:
                isMatch = true;
                useRegexp = true;
                return returnValueTab[0] + ".match(/";
            case contains:
                anyAllNoneContains = 3;
                String containString;
                if (!metadata.getClass().toString().contains("StringFunction")) {
                    if (!metadata.right().findFirst().get().getClass().toString().contains("String")) {
                        anyAllNoneContains = 1;
                        containString = returnValueTab[0] + ".every(function(element){ return ";
                    } else {
                        anyAllNoneContains = 3;
                        containString = returnValueTab[0] + ".some(function(element){return element.match(";
                    }
                } else {
                    anyAllNoneContains = 3;
                    isStartsWith = true;
                    useRegexp = true;
                    isMatch = true;
                    containString = "[" + returnValueTab[0] + "].some(function(element){return element.match(/.*";
                }
                return containString;
            case starts_with:
                isStartsWith = true;
                useRegexp = true;
                isMatch = true;
                String[] tabString = returnValueTab[0].split(" ");
                String argString = tabString[tabString.length - 1];
                return returnValueTab[0].replace(argString, "") + "[" + argString + "].some(function(element){ return" +
                        " " +
                        "element.match(/^";
            case ends_with:
                isEndsWith = true;
                useRegexp = true;
                isMatch = true;
                return "[" + returnValueTab[0] + "].some(function(element){ return element.match(/.*";
            case greater_than:
                returnValueTab[0] = writeForDiff(returnValueTab[0]);
                returnValueTab[0] += " > ";
                break;
            case greater_or_equals:
                returnValueTab[0] = writeForDiff(returnValueTab[0]);
                returnValueTab[0] += " >= ";
                break;
            case xor:
                break;
            case is:
                returnValueTab[0] += " === ";
                break;
            case lesser_than:
                returnValueTab[0] = writeForDiff(returnValueTab[0]);
                returnValueTab[0] += " < ";
                break;
            case lesser_or_equals:
                returnValueTab[0] = writeForDiff(returnValueTab[0]);
                returnValueTab[0] += " <= ";
                break;
            case has_not_size:
                returnValueTab[0] += ".length != ";
                break;
            case has_size:
                returnValueTab[0] += ".length == ";
                break;
            case is_empty:
                returnValueTab[0] += ".length == 0";
                break;
            case is_not_empty:
                returnValueTab[0] += ".length != 0";
                break;
            case length_is:
                returnValueTab[0] += ".length ";
                break;
            case lambda:
                break;
            case today:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + "moment(moment().format(\"YYYY-MM-DD\"))";
                return tmpTodayValue;
            case today_plus:
                parenthesisCount++;
                isTemporalPredicate = true;
                returnValueTab[0] += "moment(moment().format(\"YYYY-MM-DD\")).add(";
                deque = ((LeafMetadata) metadata.right().findFirst().get()).elements();
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata) + ", ";
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata);
                alreadyComputed = true;
                return returnValueTab[0] + ")";
            case today_minus:
                parenthesisCount++;
                isTemporalPredicate = true;
                returnValueTab[0] += "moment(moment().format(\"YYYY-MM-DD\")).subtract(";
                deque = ((LeafMetadata) metadata.right().findFirst().get()).elements();
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata) + ", ";
                returnValueTab[0] += writeElement(deque.pollFirst(), "", metadata);
                alreadyComputed = true;
                return returnValueTab[0] + ")";
            case first_day_of_this_month:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + "moment(moment().format(\"YYYY-MM-DD\")).startOf('month')";
                return tmpTodayValue;
            case first_day_of_this_year:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + "moment(moment().format(\"YYYY-MM-DD\")).startOf('year')";
                return tmpTodayValue;
            case last_day_of_this_month:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + "moment(moment().format(\"YYYY-MM-DD\")).endOf('month')";
                return tmpTodayValue;
            case last_day_of_this_year:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + "moment(moment().format(\"YYYY-MM-DD\")).endOf('month')";
                return tmpTodayValue;
            case first_day_of_month:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + ".startOf('month')";
                return tmpTodayValue;
            case first_day_of_next_month:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + "moment(moment().format(\"YYYY-MM-DD\")).add(1,'month').startOf" +
                        "('month')";
                return tmpTodayValue;
            case first_day_of_year:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + ".startOf('year')";
                return tmpTodayValue;
            case first_day_of_next_year:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + "moment(moment().format(\"YYYY-MM-DD\")).add(1,'year').startOf" +
                        "('year')";
                return tmpTodayValue;
            case last_day_of_month:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + ".endOf('month')";
                return tmpTodayValue;
            case last_day_of_year:
                isTemporalPredicate = true;
                tmpTodayValue = returnValueTab[0] + ".endOf('year')";
                return tmpTodayValue;
        }
        return returnValueTab[0];
    }

    private String writeForDiff(String tmpTodayValue) {
        if (isDiff) {
            tmpTodayValue = "Math.round(Math.abs(" + tmpTodayValue + "))";
            isDiff = false;
            isTemporalPredicate = false;
        }
        return tmpTodayValue;
    }

    private String writeUnary(Metadata metadata) {
        String[] returnValue = new String[1];
        returnValue[0] = "";
        UnaryMetadata unaryMetadata = (UnaryMetadata) metadata;
        DefaultOperator operator = (DefaultOperator) unaryMetadata.getOperator();
        if (operator == not) {
            // test eval_not_second_false
            returnValue[0] += "!(";
            unaryMetadata.children().forEach(elt -> returnValue[0] += writeMetadata(elt));
            returnValue[0] += ")";
        } else {
            unaryMetadata.children().forEach(elt -> returnValue[0] += writeMetadata(elt));
            returnValue[0] = writeOperator(operator, returnValue[0], unaryMetadata);
        }
        return returnValue[0];
    }

    private String writeValue(Element element, String returnValue, Metadata metadata) {
        if (!alreadyComputed) {
            if (anyAllNoneContains != -1) {
                switch (anyAllNoneContains) {
                    case 0:
                        anyAllNoneContains = -1;
                        returnValue += (isIterableOrField(metadata) ? writeValue(element, returnValue, metadata) :
                                "[" + writeValue(element, returnValue, metadata) + "]") + ".indexOf(element) >= " +
                                "0 ;})";
                        isMatch = false;
                        break;
                    case 1:
                        anyAllNoneContains = -1;
                        if (isMatch) {
                            returnValue += (isIterableOrField(metadata) ? writeValue(element, returnValue, metadata) :
                                    "[" + writeValue(element, returnValue, metadata) + "]") + ".every(function" +
                                    "(elt){ return elt.match(element);});})";
                        } else {
                            returnValue = (isIterableOrField(metadata) ? writeValue(element, returnValue, metadata) :
                                    "[" + writeValue(element, returnValue, metadata) + "]") + ".some(function(elt){ " +
                                    "return elt.match(element);});})";
                        }
                        isMatch = false;
                        break;
                    case 2:
                        anyAllNoneContains = -1;
                        returnValue += (isIterableOrField(metadata) ? writeValue(element, returnValue, metadata) :
                                "[" + writeValue(element, returnValue, metadata) + "]") + ".indexOf(element) < 0;})";
                        isMatch = false;
                        break;
                    case 3:
                        anyAllNoneContains = -1;
                        if (useRegexp) {
                            returnValue += element.toString() + ".*/);})";
                            useRegexp = false;
                        } else {
                            returnValue += ");})";
                        }
                    default:
                        break;
                }
            } else if (element.getType() == ElementType.STRING_VALUE) {
                if (isTemporalPredicate) {
                    returnValue = "moment(\'" + element.toString() + "\')";
                    if (isDiff) {
                        isDiff = false;
                        returnValue = writeForDiff(returnValue);
                    }
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
                    if (anyAllNoneContains != -1) {
                        returnValue = returnValue + "\'" + element.toString() + "\');})";
                    } else {
                        returnValue = returnValue + "\'" + element.toString() + "\'";
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
                        if (element.getReadable().toString().contains("Field")
                                || element.toString().equals("false") || element.toString().equals("true")) {
                            //eval_and_value and eval_or_value
                            returnValue = returnValue + element.toString();
                        } else {
                            returnValue = returnValue + "\'" + element.toString() + "\'";
                        }
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

    private String writeTabValues(String values) {
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
     * allow us to know if the element directly before or after the called element is an iterable field or value
     *
     * @return true if the sibling before/after the element is an iterable
     */
    private boolean isIterableOrField(Metadata metadata) {
        if (metadata.readable().startsWith(": ") || metadata.readable().startsWith(" : ")) {
            return true;
        } else if (((Element) ((LeafMetadata) metadata).elements().getFirst()).getReadable().toString().contains(
                "Iterable")) {
            return true;
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

    private void write(String str) {
        try {
            ops.write(str.getBytes(StandardCharsets.UTF_8));
        } catch (IOException ioe) {
            throw new RuntimeException(ioe);
        }
    }
}
