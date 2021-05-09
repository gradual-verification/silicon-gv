var executionTreeData = [
{"kind": "Method","value": "withdraw","open":true,
"children": [
{"type": "produce","pos": "4:14","value": "balance >= amount","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":[]},
"children": [
{"type": "evaluate","pos": "4:14","value": "balance >= amount","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _"]},
"children": [
{"type": "evaluate","pos": "4:14","value": "balance","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _"]}},
{"type": "evaluate","pos": "4:25","value": "amount","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _"]}}
]}
]},
{"type": "produce","pos": "4:35","value": "amount > 0","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12"]},
"children": [
{"type": "evaluate","pos": "4:35","value": "amount > 0","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _"]},
"children": [
{"type": "evaluate","pos": "4:35","value": "amount","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _"]}},
{"type": "evaluate","pos": "4:44","value": "0","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _"]}}
]}
]},
{"kind": "WellformednessCheck","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]},
"children": [
{"type": "produce","pos": "5:13","value": "remaining >= 0","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]},
"children": [
{"type": "evaluate","pos": "5:13","value": "remaining >= 0","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@7@12 == _"]},
"children": [
{"type": "evaluate","pos": "5:13","value": "remaining","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@7@12 == _"]}},
{"type": "evaluate","pos": "5:26","value": "0","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@7@12 == _"]}}
]}
]}
]},
{"type": "execute","pos": "7:5","value": "assert balance >= amount","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]},
"children": [
{"type": "consume","pos": "7:12","value": "balance >= amount","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]},
"children": [
{"type": "evaluate","pos": "7:12","value": "balance >= amount","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]},
"children": [
{"type": "evaluate","pos": "7:12","value": "balance","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]}},
{"type": "evaluate","pos": "7:23","value": "amount","open":true,"prestate":{"imprecise":false,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]}}
]}
]},
{"type": "wellFormedness","pos": "7:12","value": "balance >= amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]},
"children": [
{"type": "produce","pos": "7:12","value": "balance >= amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0"]},
"children": [
{"type": "evaluate","pos": "7:12","value": "balance >= amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _"]},
"children": [
{"type": "evaluate","pos": "7:12","value": "balance","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _"]}},
{"type": "evaluate","pos": "7:23","value": "amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _"]}}
]}
]},
{"type": "produce","pos": "7:12","value": "balance >= amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _"]},
"children": [
{"type": "evaluate","pos": "7:12","value": "balance >= amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _"]},
"children": [
{"type": "evaluate","pos": "7:12","value": "balance","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _"]}},
{"type": "evaluate","pos": "7:23","value": "amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _"]}}
]}
]}
]}
]},
{"type": "execute","pos": "8:5","value": "remaining := balance - amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _"]},
"children": [
{"type": "evaluate","pos": "8:18","value": "balance - amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _"]},
"children": [
{"type": "evaluate","pos": "8:18","value": "balance","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _"]}},
{"type": "evaluate","pos": "8:28","value": "amount","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@5@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _"]}}
]}
]},
{"type": "consume","pos": "5:13","value": "remaining >= 0","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@10@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _","remaining@10@12 == balance@3@12 - amount@4@12"]},
"children": [
{"type": "evaluate","pos": "5:13","value": "remaining >= 0","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@10@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _","remaining@10@12 == balance@3@12 - amount@4@12"]},
"children": [
{"type": "evaluate","pos": "5:13","value": "remaining","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@10@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _","remaining@10@12 == balance@3@12 - amount@4@12"]}},
{"type": "evaluate","pos": "5:26","value": "0","open":true,"prestate":{"imprecise":true,\n"store":[{"value":"balance -> balance@3@12","type":"Int"},{"value":"amount -> amount@4@12","type":"Int"},{"value":"remaining -> remaining@10@12","type":"Int"}],\n"heap":[],\n "optHeap":[],\n "oldHeap":[],\n "pcs":["First:($t@6@12) == _","balance@3@12 >= amount@4@12","Second:($t@6@12) == _","amount@4@12 > 0","$t@8@12 == _","$t@9@12 == _","remaining@10@12 == balance@3@12 - amount@4@12"]}}
]}
]}
]}
]
