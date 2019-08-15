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

import dk.brics.tajs.flowgraph.SourceLocation;

/**
 * Abstract super class for property references.
 */
public abstract class Property extends SyntacticReference {

    /**
     * The base value reference.
     */
    public final SyntacticReference base;

    /**
     * The register where the base value is stored.
     */
    public final int baseRegister;

    public Property(Type type, SyntacticReference base, int baseRegister, SourceLocation location) {
        super(type, location);
        this.base = base;
        this.baseRegister = baseRegister;
    }
}
