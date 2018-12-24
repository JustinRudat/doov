/*
 * Copyright 2018 Courtanet
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package io.doov.core.dsl.meta.ast;

import static io.doov.core.dsl.DOOV.alwaysFalse;
import static io.doov.core.dsl.DOOV.alwaysTrue;
import static io.doov.core.dsl.DOOV.matchAny;
import static io.doov.core.dsl.DOOV.when;
import static io.doov.core.dsl.meta.ast.HtmlAnyMatchTest.documentOf;
import static io.doov.core.dsl.meta.ast.HtmlAnyMatchTest.format;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.jsoup.nodes.Document;
import org.jsoup.nodes.Element;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import io.doov.core.dsl.lang.Result;
import io.doov.core.dsl.lang.StepCondition;

public class HtmlFailureMatchAnyTest {
    private StepCondition A, B, C, D;
    private Result result;
    private Document doc;

    @Test
    void matchAny_false_false_false_failure() {
        A = alwaysFalse("A");
        B = alwaysFalse("B");
        C = alwaysFalse("C");
        result = when(matchAny(A, B, C)).validate().withShortCircuit(false).execute();
        doc = documentOf(result);

        assertFalse(result.value());
        assertThat(doc.select("ol.dsl-ol-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-binary")).hasSize(0);
        assertThat(doc.select("li.dsl-li-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-leaf")).hasSize(3);
        assertThat(doc.select("div.percentage-value")).extracting(Element::text)
                .containsExactly("0 %", "0 %", "0 %", "0 %");
        assertThat(doc.select("span.dsl-token-operator")).extracting(Element::text)
                .containsExactly("always false", "always false", "always false");
        assertThat(doc.select("span.dsl-token-value")).extracting(Element::text)
                .containsExactly("A", "B", "C");
        assertThat(doc.select("span.dsl-token-nary")).extracting(Element::text)
                .containsExactly("match any");
    }

    @Test
    void matchAny_false_false_false_complex_failure() {
        A = alwaysFalse("A");
        B = alwaysFalse("B");
        C = alwaysTrue("C");
        D = alwaysFalse("D");
        result = when(matchAny(A, B, C.and(D))).validate().withShortCircuit(false).execute();
        doc = documentOf(result);

        assertFalse(result.value());
        assertThat(doc.select("ol.dsl-ol-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-binary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-leaf")).hasSize(2);
        assertThat(doc.select("div.percentage-value")).extracting(Element::text)
                .containsExactly("0 %", "0 %", "0 %", "100 %", "0 %");
        assertThat(doc.select("span.dsl-token-operator")).extracting(Element::text)
                .containsExactly("always false", "always false", "always true", "always false");
        assertThat(doc.select("span.dsl-token-value")).extracting(Element::text)
                .containsExactly("A", "B", "C", "D");
        assertThat(doc.select("span.dsl-token-nary")).extracting(Element::text)
                .containsExactly("match any");
    }

    @Test
    void matchAny_true_false_false_failure() {
        A = alwaysTrue("A");
        B = alwaysFalse("B");
        C = alwaysFalse("C");
        result = when(matchAny(A, B, C)).validate().withShortCircuit(false).execute();
        doc = documentOf(result);

        assertTrue(result.value());
        assertThat(doc.select("ol.dsl-ol-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-binary")).hasSize(0);
        assertThat(doc.select("li.dsl-li-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-leaf")).hasSize(3);
        assertThat(doc.select("div.percentage-value")).extracting(Element::text)
                .containsExactly("100 %", "100 %", "0 %", "0 %");
        assertThat(doc.select("span.dsl-token-operator")).extracting(Element::text)
                .containsExactly("always true", "always false", "always false");
        assertThat(doc.select("span.dsl-token-value")).extracting(Element::text)
                .containsExactly("A", "B", "C");
        assertThat(doc.select("span.dsl-token-nary")).extracting(Element::text)
                .containsExactly("match any");
    }

    @Test
    void matchAny_false_true_true_failure() {
        A = alwaysFalse("A");
        B = alwaysTrue("B");
        C = alwaysTrue("C");
        result = when(matchAny(A, B, C)).validate().withShortCircuit(false).execute();
        doc = documentOf(result);

        assertTrue(result.value());
        assertThat(doc.select("ol.dsl-ol-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-binary")).hasSize(0);
        assertThat(doc.select("li.dsl-li-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-leaf")).hasSize(3);
        assertThat(doc.select("div.percentage-value")).extracting(Element::text)
                .containsExactly("100 %", "0 %", "100 %", "100 %");
        assertThat(doc.select("span.dsl-token-operator")).extracting(Element::text)
                .containsExactly("always false", "always true", "always true");
        assertThat(doc.select("span.dsl-token-value")).extracting(Element::text)
                .containsExactly("A", "B", "C");
        assertThat(doc.select("span.dsl-token-nary")).extracting(Element::text)
                .containsExactly("match any");
    }

    @Test
    void matchAny_true_true_true_failure() {
        A = alwaysTrue("A");
        B = alwaysTrue("B");
        C = alwaysTrue("C");
        result = when(matchAny(A, B, C)).validate().withShortCircuit(false).execute();
        doc = documentOf(result);

        assertTrue(result.value());
        assertThat(doc.select("ol.dsl-ol-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-binary")).hasSize(0);
        assertThat(doc.select("li.dsl-li-nary")).hasSize(1);
        assertThat(doc.select("li.dsl-li-leaf")).hasSize(3);
        assertThat(doc.select("div.percentage-value")).extracting(Element::text)
                .containsExactly("100 %", "100 %", "100 %", "100 %");
        assertThat(doc.select("span.dsl-token-operator")).extracting(Element::text)
                .containsExactly("always true", "always true", "always true");
        assertThat(doc.select("span.dsl-token-value")).extracting(Element::text)
                .containsExactly("A", "B", "C");
        assertThat(doc.select("span.dsl-token-nary")).extracting(Element::text)
                .containsExactly("match any");
    }

    @AfterEach
    void afterEach() {
        System.out.println(format(result, doc));
    }
}
