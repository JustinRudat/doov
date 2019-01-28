/*
 * Copyright (C) by Courtanet, All Rights Reserved.
 */
package io.doov.js.ast;

import static org.apache.commons.lang3.StringUtils.isNumeric;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.lang3.StringUtils;

import io.doov.core.dsl.lang.ValidationRule;
import io.doov.core.dsl.meta.*;

public class JavascriptWriter {

    protected final OutputStream ops;
    protected ValidationRule rule;

    private String output;
    private int anyAllNoneContains = -1;
    private int parenthesisCount = 0;
    private boolean isAgeAtOperator = false;
    private boolean useRegexp = false;
    private boolean isMatch = false;
    private boolean isStartsWith = false;
    private boolean isEndsWith = false;
    private boolean isXOR = false;
    private boolean firstPassage = true;
    private boolean isTemporalPredicate = false;
    private boolean alreadyComputed = false;
    private boolean isDiff = false;
    private boolean isBeforeOrAfter = false;
    private String leftXOR = "";

    public JavascriptWriter(OutputStream ops) {
        this.ops = ops;
        this.output = "";
    }

    public void writeRule(ValidationRule rule) {
        this.rule = rule;
        writeWhen(rule.metadata());
    }

    public void writeWhen(Metadata whenMetadata) {
        Metadata predicate = whenMetadata.children().findFirst().get().children().findFirst().get();
        String typePredicate = predicate.type().toString();
        if (typePredicate.startsWith("NARY")) {
            writeNaryMetadata(whenMetadata.children().findFirst().get());
        } else if (typePredicate.startsWith("BIN")) {
            output += "(";
            if (predicate.children().findFirst().get().type().toString().startsWith("NARY")) {
                writeNaryMetadata(predicate);
            } else {
                writeMetadata(whenMetadata);
            }
            output += ")";
        } else {
            writeMetadata(whenMetadata);
            if (isXOR) {
                output = manageXOR(output, firstPassage);
                isXOR = false;
            }
            while (parenthesisCount > 0) {
                output += ")";
                parenthesisCount--;
            }
        }
        output = "if(" + output + ") { true; } else { false; }\n";
        write(output);
        output = "";
    }

    private String writeNaryMetadata(Metadata metadata) {
        DefaultOperator operator =
                (DefaultOperator) metadata.children().findFirst().get().flatten().get(0).getReadable();
        switch (operator) {
            case min:
                output += "Math.min.apply(null,[";
                break;
            case match_none:
                output += "!";
                break;
            case count:
            case sum:
                output += "[";
                break;
        }
        metadata.children().forEach(child -> child.children().forEach(elt ->
        {
            if (elt.type().toString().startsWith("BIN")) {
                output += "(";
                writeMetadata(elt);
                output += ")";
            } else {
                writeMetadata(elt);
            }
            if (!elt.equals(child.children().skip(child.children().count() - 1).findFirst().get())) {
                switch (operator) {
                    case match_any:
                        output += " || ";                       // using 'or' operator to match any of the predicate
                        // given
                        break;
                    case match_all:
                        output += " && ";                       // using 'and' operator for match all
                        break;
                    case match_none:
                        output += " && !";                      // 'and not' for match none
                        break;
                    case min:
                    case sum:
                    case count:
                        output += ", ";                         // separating the list values
                        break;
                }
            }
        }));
        switch (operator) {
            case count:
                output += "].reduce(function(acc,val){if(val){return acc+1;}return acc;},0)";
                break;
            case min:
                output += "])";
                break;
            case sum:
                output += "].reduce(function(acc,val){ return acc+val;},0)";
                break;
        }
        return output;
    }

    public void writeMetadata(Metadata metadata) {
        if (metadata.children().count() >= 1) {
            if (metadata.children().findFirst().get().type().toString().startsWith("NARY")) {
                writeNaryMetadata(metadata.children().findFirst().get());
            } else {
                writeMetadata(metadata.children().findFirst().get());
            }
        } else {
            List<Element> listMetadata = metadata.flatten();
            String[] internOutput = new String[1];
            internOutput[0] = "";
            listMetadata.stream().forEach(element -> {
                switch (element.getType()) {
                    case FIELD:
                        internOutput[0] = writeField(element, internOutput[0]);
                        break;
                    case OPERATOR:
                        internOutput[0] = writeOperator(element, internOutput[0]);
                        break;
                    case VALUE:
                    case STRING_VALUE:
                        internOutput[0] = writeValue(element, internOutput[0]);
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
            output += internOutput[0];
        }
    }

    public String writeValue(Element element, String internOutput) {
        if (!alreadyComputed) {
            if (element.toString().startsWith(" : ")) {
                internOutput = internOutput + manageTabValues(element.toString().replace(" : ", ""));
            } else if (element.getType() == ElementType.STRING_VALUE) {
                if (useRegexp) {
                    useRegexp = false;
                    if (isMatch) {
                        isMatch = false;
                        if (isStartsWith) {
                            isStartsWith = false;
                            internOutput = internOutput + formatRegexp(element.toString()) + ".*/);})";
                        } else if (isEndsWith) {
                            isEndsWith = false;
                            internOutput = internOutput + formatRegexp(element.toString()) + "$/);})";
                        } else {
                            internOutput = internOutput + element.toString() + "/)";
                        }
                    } else {
                        internOutput = internOutput + formatRegexp(element.toString());
                    }
                } else {
                    if (useRegexp) {
                        useRegexp = false;
                        internOutput = internOutput + "\'" + element.toString() + "\'.*/);})";
                    } else {
                        if (anyAllNoneContains != -1) {
                            internOutput = internOutput + "\'" + element.toString() + "\');})";
                        } else {
                            internOutput = internOutput + "\'" + element.toString() + "\'";
                        }
                    }

                }
            } else {
                if (StringUtils.isNumeric(element.toString())) {
                    internOutput = internOutput + element.toString();
                } else {
                    if (isTemporalPredicate) {
                        isTemporalPredicate = false;

                        internOutput = internOutput + "\'" + element.toString() + "\'";
                    } else {
                        internOutput = internOutput + element.toString();
                    }
                }
            }
        }
        alreadyComputed = false;
        return internOutput;
    }

    public String writeField(Element element, String internOutput) {
        if (alreadyComputed) {
            alreadyComputed = false;
            return internOutput;
        } else {
            if(element.getReadable().toString().contains("Date")){
                return internOutput + "moment(" + element.toString() + ")";
            } else if (isTemporalPredicate) {
                isTemporalPredicate = false;
                if(isDiff) {
                    return internOutput + "moment(" + element.toString() + ")";
                }

            }
            return internOutput + element.toString();
        }
    }

    public String writeOperator(Element element, String internOutput) {
        List<Element> flatList;
        String numValue;
        String tempValue;
        String tmpTodayValue;
        DefaultOperator operator = (DefaultOperator) element.getReadable();
        switch (operator) {
            case empty:
                break;
            case and:
                return internOutput + " && ";
            case or:
                return internOutput + " || ";
            case match_any:
                anyAllNoneContains = 0;
                isMatch = true;
                return isSiblingIterable(element, true) ? internOutput + ".some(function(element){ return "
                        : "[" + internOutput + "].some(function(element){ return ";
            case match_all:
                anyAllNoneContains = 1;
                isMatch = true;
                return isSiblingIterable(element, true) ? internOutput + ".every(function(element){ return "
                        : "[" + internOutput + "].every(function(element){ return ";
            case match_none:
                anyAllNoneContains = 2;
                isMatch = true;
                return isSiblingIterable(element, true) ? internOutput + ".every(function(element){ return "
                        : "[" + internOutput + "].every(function(element){ return ";
            case count:
                break;
            case sum:
                break;
            case min:
                break;
            case not:
                parenthesisCount++;
                return "!(" + internOutput;
            case always_true:
                return internOutput + " == true";
            case always_false:
                return internOutput + " == false";
            case times:
                return internOutput + " * ";
            case equals:
                flatList = rule.metadata().flatten();
                if (isDiff) {
                    internOutput = internOutput + ",\'years\')))";
                }
                if (flatList.get(flatList.indexOf(element) - 1).getReadable().toString().contains("LocalDate")
                        || isTemporalPredicate && !isDiff) {
                    parenthesisCount++;
                    return "moment(" + internOutput + ").isSame(";
                } else {
                    isDiff = false;
                    isTemporalPredicate = false;
                    return internOutput + " == ";
                }
            case not_equals:
                return internOutput + " != ";
            case is_null:
                return internOutput + " === (null || undefined || \"\")";
            case is_not_null:
                return internOutput + " !== (null && undefined && \"\")";
            case as_a_number:
                break;
            case as_string:
                break;
            case as:
                break;
            case minus:
                isTemporalPredicate = true;
                alreadyComputed = true;
                flatList = rule.metadata().flatten();
                numValue = flatList.get(flatList.indexOf(element) + 1).toString();
                tempValue = flatList.get(flatList.indexOf(element) + 2).toString();
                if(isBeforeOrAfter){
                    isBeforeOrAfter = false;
                    parenthesisCount--;
                    internOutput += ")";
                }
                return internOutput + ".subtract(" + numValue + ",\'" + tempValue + "\')";
            case plus:
                isTemporalPredicate = true;
                alreadyComputed = true;
                flatList = rule.metadata().flatten();
                numValue = flatList.get(flatList.indexOf(element) + 1).toString();
                tempValue = flatList.get(flatList.indexOf(element) + 2).toString();
                if(isBeforeOrAfter){
                    isBeforeOrAfter = false;
                    parenthesisCount--;
                    internOutput += ")";
                }
                return internOutput + ".add(" + numValue + ",\'" + tempValue + "\')";
            case after:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                isBeforeOrAfter = true;
                return "moment(" + internOutput + ").isAfter(moment(";
            case after_or_equals:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                isBeforeOrAfter = true;
                return "moment(" + internOutput + ").isSameOrAfter(moment(";
            case age_at:
                isAgeAtOperator = true;
                isTemporalPredicate = true;
                isDiff = true;
                return "Math.round(Math.abs(moment(" + internOutput + ").diff(";
            case before:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                isBeforeOrAfter = true;
                return "moment(" + internOutput + ").isBefore(moment(";
            case before_or_equals:
                isTemporalPredicate = true;
                parenthesisCount += 2;
                isBeforeOrAfter = true;
                return "moment(" + internOutput + ").isSameOrBefore(moment(";
            case matches:
                isMatch = true;
                useRegexp = true;
                return internOutput + ".match(/";
            case contains:
                String containString;
                if (isSiblingIterable(element, true)) {
                    if (isSiblingIterable(element, false)) {
                        anyAllNoneContains = 1;
                        containString = internOutput + ".every(function(element){ return ";
                    } else {
                        anyAllNoneContains = 3;
                        containString = internOutput + ".some(function(element){return element.match(";
                    }
                } else {
                    anyAllNoneContains = 3;
                    isStartsWith = true;
                    useRegexp = true;
                    isMatch = true;
                    containString = "[" + internOutput + "].some(function(element){return element.match(/.*";
                }
                return containString;
            case starts_with:
                isStartsWith = true;
                useRegexp = true;
                isMatch = true;
                String[] tabString = internOutput.split(" ");
                String argString = tabString[tabString.length - 1];
                return internOutput.replace(argString, "") + "[" + argString + "].some(function(element){ return " +
                        "element.match(/^";
            case ends_with:
                isEndsWith = true;
                useRegexp = true;
                isMatch = true;
                return "[" + internOutput + "].some(function(element){ return element.match(/.*";
            case greater_than:
                if(isDiff){
                    isDiff = false;
                    internOutput += ",\'years\')))";
                }
                return internOutput + " > ";
            case greater_or_equals:
                if(isDiff){
                    isDiff = false;
                    internOutput += ",\'years\')))";
                }
                return internOutput + " >= ";
            case xor:
                isXOR = true;
                manageXOR(internOutput, firstPassage);
                return internOutput;
            case is:
                if(isDiff){
                    isDiff = false;
                    internOutput += ",\'years\')))";
                }
                return internOutput + " === ";
            case lesser_than:
                if(isDiff){
                    isDiff = false;
                    internOutput += ",\'years\')))";
                }
                return internOutput + " < ";
            case lesser_or_equals:
                if(isDiff){
                    isDiff = false;
                    internOutput += ",\'years\')))";
                }
                return internOutput + " <= ";
            case has_not_size:
                return internOutput + ".length != ";
            case has_size:
                return internOutput + ".length == ";
            case is_empty:
                return internOutput + ".length == 0";
            case is_not_empty:
                return internOutput + ".length != 0";
            case length_is:
                return internOutput + ".length";
            case today:
                isTemporalPredicate = true;
//                if (isDiff) {
//                    isDiff = false;
//                    isTemporalPredicate = false;
//                    return internOutput + "moment(moment().format(\"YYYY-MM-DD\")),\'years\')))";
//                } else {
                    return internOutput + "moment(moment().format(\"YYYY-MM-DD\"))";
//                }
            case today_plus:
                parenthesisCount++;
                isTemporalPredicate = true;
                return "moment().add(";
            case today_minus:
                parenthesisCount++;
                isTemporalPredicate = true;
                return "moment().add(";
            case first_day_of_this_month:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + "moment().startOf('month')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case first_day_of_this_year:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + "moment().startOf('year')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case last_day_of_this_month:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + "moment().endOf('month')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case last_day_of_this_year:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + "moment().endOf('month')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case first_day_of_month:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + ".startOf('month')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case first_day_of_next_month:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + "moment().add(1,'month').startOf('month')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case first_day_of_year:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + ".startOf('year')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case first_day_of_next_year:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + "moment().add(1,'year').startOf('year')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case last_day_of_month:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + ".endOf('month')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            case last_day_of_year:
                isTemporalPredicate = true;
                tmpTodayValue = internOutput + ".endOf('year')";
                if (isDiff) {
                    isDiff = false;
                    tmpTodayValue += ",\'years\')))";
                }
                return tmpTodayValue;
            default:
                break;
        }
        return internOutput;
    }

    private void resetTemporalBoolean() {
        if (isTemporalPredicate) {
            isTemporalPredicate = false;
        }
        if (isDiff) {
            isDiff = false;
        }
    }

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

    private String manageXOR(String internOutput, boolean firstPassage) {
        String xorString = "";
        if (firstPassage) {
            leftXOR = internOutput;
            this.firstPassage = false;
        } else {
            String rightXOR = internOutput.replace(leftXOR, "");
            xorString = "(!" + leftXOR + " && " + rightXOR + ") || (" + leftXOR + " && !" + rightXOR + ")";
            this.firstPassage = true;
        }
        return xorString;
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
