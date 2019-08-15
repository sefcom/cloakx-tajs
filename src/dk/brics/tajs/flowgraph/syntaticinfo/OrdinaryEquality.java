/*
 * Copyright 2009-2017 Aarhus University
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

package dk.brics.tajs.flowgraph.syntaticinfo;

/**
 * An equality comparison between two values in a condition.
 */
public class OrdinaryEquality extends AbstractEquality {

    public OrdinaryEquality(SyntacticReference reference, int comparateeRegister, boolean isStrict, boolean negated) {
        super(reference, comparateeRegister, isStrict, negated);
    }

    public <T> T accept(ConditionPatternVisitor<T> v) {
        return v.visit(this);
    }
}
