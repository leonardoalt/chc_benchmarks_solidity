(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_A_19_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_19_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_19_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_3_function_f__11_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_function_proxy__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_5_function_proxy__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (nondet_interface_1_A_19_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_1 x_3_1) true) (and (= error_0 0) (summary_5_function_proxy__18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2))) (nondet_interface_1_A_19_0 error_1 this_0 abi_0 crypto_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |interface_6_C_44_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_7_C_44_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_8_C_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (= error_1 0) (nondet_interface_7_C_44_0 error_1 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_9_function_f__11_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_10_function_proxy__18_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_11_function_proxy__18_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (nondet_interface_7_C_44_0 error_1 this_0 abi_0 crypto_0 state_0 x_3_0 state_1 x_3_1) true) (and (= error_1 0) (summary_11_function_proxy__18_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2))) (nondet_interface_7_C_44_0 error_2 this_0 abi_0 crypto_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |summary_12_function_f__43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_13_D_69_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_14_D_69_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_15_D_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (= error_2 0) (nondet_interface_14_D_69_0 error_2 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_16_function_f__11_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_17_function_proxy__18_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_18_function_proxy__18_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (nondet_interface_14_D_69_0 error_2 this_0 abi_0 crypto_0 state_0 x_3_0 state_1 x_3_1) true) (and (= error_2 0) (summary_18_function_proxy__18_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2))) (nondet_interface_14_D_69_0 error_3 this_0 abi_0 crypto_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |summary_19_function_f__43_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_20_function_f__68_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_21_function_f__11_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_22_f_10_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(block_21_function_f__11_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_21_function_f__11_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_22_f_10_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_23_return_function_f__11_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_22_f_10_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_8_1) (and (=> true (and (>= expr_8_1 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_8_1 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_8_1 expr_7_0) (and (=> true (and (>= expr_6_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_6_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_6_0 x_3_1) (and (=> true true) (and (= expr_7_0 2) true)))))))) true) (block_23_return_function_f__11_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_23_return_function_f__11_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_3_function_f__11_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_24_function_proxy__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_25_proxy_17_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(block_24_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_24_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_25_proxy_17_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_26_return_function_proxy__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_27_function_f__11_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (summary_3_function_f__11_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_27_function_f__11_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_25_proxy_17_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_27_function_f__11_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (summary_4_function_proxy__18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_25_proxy_17_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_27_function_f__11_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (block_26_return_function_proxy__18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_26_return_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_4_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_28_function_proxy__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(block_28_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_28_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_4_function_proxy__18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_3_1 state_3 x_3_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3965020297)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 236)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 85)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 104)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 137)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true))))))) true) (summary_5_function_proxy__18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (interface_0_A_19_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_5_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 0))) (interface_0_A_19_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |contract_initializer_29_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_30_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (contract_initializer_entry_30_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_after_init_31_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_entry_30_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 0) true)))) true) (contract_initializer_after_init_31_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_after_init_31_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_29_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_32_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_32_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_32_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_29_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_2_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_32_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= error_1 0) (and (contract_initializer_29_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))) true) (summary_constructor_2_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (summary_constructor_2_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_19_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_33_function_f__11_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_34_f_10_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_33_function_f__11_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_33_function_f__11_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_34_f_10_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_35_return_function_f__11_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_34_f_10_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_8_1) (and (=> true (and (>= expr_8_1 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_8_1 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_8_1 expr_7_0) (and (=> true (and (>= expr_6_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_6_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_6_0 x_3_1) (and (=> true true) (and (= expr_7_0 2) true)))))))) true) (block_35_return_function_f__11_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_35_return_function_f__11_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_9_function_f__11_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_36_function_proxy__18_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_37_proxy_17_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_36_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_36_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_37_proxy_17_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_38_return_function_proxy__18_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_39_function_f__43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (summary_12_function_f__43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_39_function_f__43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_37_proxy_17_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_39_function_f__43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (summary_10_function_proxy__18_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_37_proxy_17_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_39_function_f__43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (block_38_return_function_proxy__18_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_38_return_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_10_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_40_function_proxy__18_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_40_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_40_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_10_function_proxy__18_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_3_1 state_3 x_3_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_1_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_1_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_1_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_1_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3965020297)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 236)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 85)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 104)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 137)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true))))))) true) (summary_11_function_proxy__18_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (interface_6_C_44_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_11_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 0))) (interface_6_C_44_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_41_function_f__43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_42_f_42_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_41_function_f__43_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_41_function_f__43_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_42_f_42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_43_return_function_f__43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_44_function_f__11_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (summary_9_function_f__11_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_44_function_f__11_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_2_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_42_f_42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_44_function_f__11_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (summary_12_function_f__43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_45_function_f__43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_42_f_42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_31_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_31_0 x_3_2) (and (= error_1 0) (and (summary_44_function_f__11_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)))))))) (and (not expr_33_1) (= error_2 2))) (block_45_function_f__43_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_45_function_f__43_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_12_function_f__43_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_46_function_f__43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_42_f_42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_39_1 (= expr_37_0 expr_38_0)) (and (=> true true) (and (= expr_38_0 3) (and (=> true (and (>= expr_37_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_37_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_37_0 x_3_2) (and (= error_2 error_1) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_31_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_31_0 x_3_2) (and (= error_1 0) (and (summary_44_function_f__11_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)))))))))))))) (and (not expr_39_1) (= error_3 3))) (block_46_function_f__43_44_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_46_function_f__43_44_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_12_function_f__43_44_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_42_f_42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_3 error_2) (and (= expr_39_1 (= expr_37_0 expr_38_0)) (and (=> true true) (and (= expr_38_0 3) (and (=> true (and (>= expr_37_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_37_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_37_0 x_3_2) (and (= error_2 error_1) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_31_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_31_0 x_3_2) (and (= error_1 0) (and (summary_44_function_f__11_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))))))))))))))) true) (block_43_return_function_f__43_44_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_43_return_function_f__43_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_12_function_f__43_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_47_C_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_48_C_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (contract_initializer_entry_48_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_after_init_49_C_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_48_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_after_init_49_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_49_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_47_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_50_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_51_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (contract_initializer_entry_51_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_after_init_52_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_51_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 0) true)))) true) (contract_initializer_after_init_52_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_52_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_50_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_53_C_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_53_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_53_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_50_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_8_C_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_53_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_47_C_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_3_2 x_3_3) (and (= error_1 0) (and (contract_initializer_50_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_8_C_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_3_0 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_53_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= error_2 0) (and (contract_initializer_47_C_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_3_2 x_3_3) (and (= error_1 0) (and (contract_initializer_50_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))) true) (summary_constructor_8_C_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_3_0 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (summary_constructor_8_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_6_C_44_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_54_function_f__11_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_55_f_10_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_54_function_f__11_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_54_function_f__11_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_55_f_10_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_56_return_function_f__11_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_55_f_10_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_8_1) (and (=> true (and (>= expr_8_1 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_8_1 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_8_1 expr_7_0) (and (=> true (and (>= expr_6_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_6_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_6_0 x_3_1) (and (=> true true) (and (= expr_7_0 2) true)))))))) true) (block_56_return_function_f__11_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_56_return_function_f__11_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_16_function_f__11_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_57_function_proxy__18_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_58_proxy_17_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_57_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_57_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_58_proxy_17_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_59_return_function_proxy__18_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_60_function_f__68_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (summary_20_function_f__68_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_60_function_f__68_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_58_proxy_17_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_60_function_f__68_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (summary_17_function_proxy__18_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_58_proxy_17_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_60_function_f__68_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (block_59_return_function_proxy__18_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_59_return_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_17_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_61_function_proxy__18_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_61_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_61_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_17_function_proxy__18_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_3_1 state_3 x_3_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3965020297)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 236)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 85)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 104)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 137)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true))))))) true) (summary_18_function_proxy__18_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (interface_13_D_69_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_18_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 0))) (interface_13_D_69_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_62_function_f__43_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_63_f_42_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_62_function_f__43_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_62_function_f__43_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_63_f_42_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_64_return_function_f__43_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_65_function_f__11_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (summary_16_function_f__11_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_65_function_f__11_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_63_f_42_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_65_function_f__11_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (summary_19_function_f__43_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_66_function_f__43_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_63_f_42_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_31_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_31_0 x_3_2) (and (= error_1 0) (and (summary_65_function_f__11_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)))))))) (and (not expr_33_1) (= error_2 5))) (block_66_function_f__43_69_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_66_function_f__43_69_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_19_function_f__43_69_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_67_function_f__43_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_63_f_42_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_39_1 (= expr_37_0 expr_38_0)) (and (=> true true) (and (= expr_38_0 3) (and (=> true (and (>= expr_37_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_37_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_37_0 x_3_2) (and (= error_2 error_1) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_31_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_31_0 x_3_2) (and (= error_1 0) (and (summary_65_function_f__11_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)))))))))))))) (and (not expr_39_1) (= error_3 6))) (block_67_function_f__43_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_67_function_f__43_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_19_function_f__43_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_63_f_42_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_3 error_2) (and (= expr_39_1 (= expr_37_0 expr_38_0)) (and (=> true true) (and (= expr_38_0 3) (and (=> true (and (>= expr_37_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_37_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_37_0 x_3_2) (and (= error_2 error_1) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_31_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_31_0 x_3_2) (and (= error_1 0) (and (summary_65_function_f__11_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))))))))))))))) true) (block_64_return_function_f__43_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_64_return_function_f__43_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_19_function_f__43_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_68_function_f__68_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_69_f_67_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_68_function_f__68_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_68_function_f__68_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_69_f_67_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_70_return_function_f__68_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_71_function_f__43_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (summary_19_function_f__43_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_71_function_f__43_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_69_f_67_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_71_function_f__43_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (summary_20_function_f__68_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_72_function_f__68_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_69_f_67_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_58_1 (= expr_56_0 expr_57_0)) (and (=> true true) (and (= expr_57_0 2) (and (=> true (and (>= expr_56_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_56_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_56_0 x_3_2) (and (= error_1 0) (and (summary_71_function_f__43_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)))))))) (and (not expr_58_1) (= error_2 7))) (block_72_function_f__68_69_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_72_function_f__68_69_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_20_function_f__68_69_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_73_function_f__68_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_69_f_67_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_64_1 (= expr_62_0 expr_63_0)) (and (=> true true) (and (= expr_63_0 3) (and (=> true (and (>= expr_62_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_62_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_62_0 x_3_2) (and (= error_2 error_1) (and (= expr_58_1 (= expr_56_0 expr_57_0)) (and (=> true true) (and (= expr_57_0 2) (and (=> true (and (>= expr_56_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_56_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_56_0 x_3_2) (and (= error_1 0) (and (summary_71_function_f__43_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)))))))))))))) (and (not expr_64_1) (= error_3 8))) (block_73_function_f__68_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_73_function_f__68_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2) (summary_20_function_f__68_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_69_f_67_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_3 error_2) (and (= expr_64_1 (= expr_62_0 expr_63_0)) (and (=> true true) (and (= expr_63_0 3) (and (=> true (and (>= expr_62_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_62_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_62_0 x_3_2) (and (= error_2 error_1) (and (= expr_58_1 (= expr_56_0 expr_57_0)) (and (=> true true) (and (= expr_57_0 2) (and (=> true (and (>= expr_56_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_56_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_56_0 x_3_2) (and (= error_1 0) (and (summary_71_function_f__43_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))))))))))))))) true) (block_70_return_function_f__68_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_70_return_function_f__68_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_20_function_f__68_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_74_D_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_75_D_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (contract_initializer_entry_75_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_after_init_76_D_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_75_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_after_init_76_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_76_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_74_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_77_C_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_78_C_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (contract_initializer_entry_78_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_after_init_79_C_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_78_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_after_init_79_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_79_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_77_C_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_80_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_81_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (contract_initializer_entry_81_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_after_init_82_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_81_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 0) true)))) true) (contract_initializer_after_init_82_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_82_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_80_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_83_D_69_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_83_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_83_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_80_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_15_D_69_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_83_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_77_C_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_3_2 x_3_3) (and (= error_1 0) (and (contract_initializer_80_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_15_D_69_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_3_0 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_83_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_74_D_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_3_3 x_3_4) (and (= error_2 0) (and (contract_initializer_77_C_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_3_2 x_3_3) (and (= error_1 0) (and (contract_initializer_80_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))))) (> error_3 0)) (summary_constructor_15_D_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_3_0 x_3_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_83_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= error_3 0) (and (contract_initializer_74_D_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_3_3 x_3_4) (and (= error_2 0) (and (contract_initializer_77_C_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_3_2 x_3_3) (and (= error_1 0) (and (contract_initializer_80_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))))) true) (summary_constructor_15_D_69_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_3_0 x_3_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (summary_constructor_15_D_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_13_D_69_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |error_target_9_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (interface_0_A_19_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_5_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 2))) error_target_9_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (interface_6_C_44_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_11_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 2))) error_target_9_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (interface_13_D_69_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_18_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 2))) error_target_9_0)))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (interface_0_A_19_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_5_function_proxy__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 3))) error_target_10_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (interface_6_C_44_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_11_function_proxy__18_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 3))) error_target_10_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (interface_13_D_69_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_18_function_proxy__18_69_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (= error_0 3))) error_target_10_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 |tuple()|) (expr_28_1 |tuple()|) (expr_2_0 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_53_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> error_target_10_0 false)))
(check-sat)