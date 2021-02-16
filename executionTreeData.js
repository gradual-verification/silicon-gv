var executionTreeData = [
{"kind": "Method","value": "test01","open":true,
"children": [
{"type": "produce","pos": "4:12","value": "x == null","open":true,"prestate":{"store":[{"value":"x -> x@2@12","type":"Ref"},{"value":"b -> b@3@12","type":"Bool"}],"heap":[],"oldHeap":[],"pcs":[]},
"children": [
{"type": "evaluate","pos": "4:12","value": "x == null","open":true,"prestate":{"store":[{"value":"x -> x@2@12","type":"Ref"},{"value":"b -> b@3@12","type":"Bool"}],"heap":[],"oldHeap":[],"pcs":["First:($t@4@12) == _"]},
"children": [
{"type": "evaluate","pos": "4:12","value": "x","open":true,"prestate":{"store":[{"value":"x -> x@2@12","type":"Ref"},{"value":"b -> b@3@12","type":"Bool"}],"heap":[],"oldHeap":[],"pcs":["First:($t@4@12) == _"]}},
{"type": "evaluate","pos": "4:17","value": "null","open":true,"prestate":{"store":[{"value":"x -> x@2@12","type":"Ref"},{"value":"b -> b@3@12","type":"Bool"}],"heap":[],"oldHeap":[],"pcs":["First:($t@4@12) == _"]}}
]}
]},
{"type": "produce","pos": "4:25","value": "acc(x.f, write)","open":true,"prestate":{"store":[{"value":"x -> x@2@12","type":"Ref"},{"value":"b -> b@3@12","type":"Bool"}],"heap":[],"oldHeap":[],"pcs":["First:($t@4@12) == _","x@2@12 == Null"]},
"children": [
{"type": "evaluate","pos": "4:29","value": "x","open":true,"prestate":{"store":[{"value":"x -> x@2@12","type":"Ref"},{"value":"b -> b@3@12","type":"Bool"}],"heap":[],"oldHeap":[],"pcs":["First:($t@4@12) == _","x@2@12 == Null"]}},
{"type": "evaluate","pos": "4:25","value": "write","open":true,"prestate":{"store":[{"value":"x -> x@2@12","type":"Ref"},{"value":"b -> b@3@12","type":"Bool"}],"heap":[],"oldHeap":[],"pcs":["First:($t@4@12) == _","x@2@12 == Null"]}}
]},
{"kind": "WellformednessCheck","open":true,"prestate":{"store":[{"value":"x -> x@2@12","type":"Ref"},{"value":"b -> b@3@12","type":"Bool"}],"heap":[],"oldHeap":[],"pcs":["First:($t@4@12) == _","x@2@12 == Null"]}}
]}
]
