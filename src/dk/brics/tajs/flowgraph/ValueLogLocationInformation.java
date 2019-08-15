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

package dk.brics.tajs.flowgraph;

import java.util.Map;
import java.util.Set;

import static dk.brics.tajs.util.Collections.newMap;
import static dk.brics.tajs.util.Collections.newSet;

/**
 * Log files from the value logger uses slightly different source location than TAJS for some syntactic constructs. This class contains information for mapping between the two domains.
 */
public class ValueLogLocationInformation {

    private final Map<SourceLocation, Set<SourceLocation>> tajsLocation2jalangiLocation;

    private final Set<SourceLocation> declaredAccessorAllocationSites;

    public ValueLogLocationInformation() {
        tajsLocation2jalangiLocation = newMap();
        declaredAccessorAllocationSites = newSet();
    }

    public Map<SourceLocation, Set<SourceLocation>> getTajsLocation2jalangiLocation() {
        return tajsLocation2jalangiLocation;
    }

    public Set<SourceLocation> getDeclaredAccessorAllocationSites() {
        return declaredAccessorAllocationSites;
    }
}
