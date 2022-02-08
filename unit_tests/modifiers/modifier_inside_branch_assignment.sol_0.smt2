(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_47_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_1_C_47_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_2_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (owner_4_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_47_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 owner_4_0 state_0 x_2_0 owner_4_0))))


(declare-fun |summary_3_function_f__23_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_f__23_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_C_47_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) true) (and (= error_0 0) (summary_4_function_f__23_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 owner_4_1 state_2 x_2_2 owner_4_2))) (nondet_interface_1_C_47_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 owner_4_0 state_2 x_2_2 owner_4_2))))


(declare-fun |summary_5_function_g__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_6_function_g__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (nondet_interface_1_C_47_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) true) (and (= error_1 0) (summary_6_function_g__46_47_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 owner_4_1 y_25_0 state_2 x_2_2 owner_4_2 y_25_1))) (nondet_interface_1_C_47_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 owner_4_0 state_2 x_2_2 owner_4_2))))


(declare-fun |block_7_function_f__23_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_8_f_22_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(block_7_function_f__23_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_7_function_f__23_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_2_1 x_2_0)) (= owner_4_1 owner_4_0))) true) true)) true) (block_8_f_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1))))


(declare-fun |block_9_return_f_13_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_10_if_header_f_11_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_11_if_true_f_10_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_12_f_22_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_8_f_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) true) true) (block_10_if_header_f_11_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_10_if_header_f_11_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) (and (= expr_9_1 (= expr_7_1 expr_8_0)) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 1461501637330902918203684832716283019655932542975))) (and (= expr_8_0 owner_4_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 1461501637330902918203684832716283019655932542975))) (and (= expr_7_1 (|msg.sender| tx_0)) true)))))) expr_9_1) (block_11_if_true_f_10_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_10_if_header_f_11_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) (and (= expr_9_1 (= expr_7_1 expr_8_0)) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 1461501637330902918203684832716283019655932542975))) (and (= expr_8_0 owner_4_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 1461501637330902918203684832716283019655932542975))) (and (= expr_7_1 (|msg.sender| tx_0)) true)))))) (not expr_9_1)) (block_12_f_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1))))


(declare-fun |block_13_return_function_f__23_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_11_if_true_f_10_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) (and (= x_2_2 expr_20_1) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 expr_19_0) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 x_2_1) (and (=> true true) (and (= expr_19_0 0) true)))))))) true) (block_13_return_function_f__23_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_2 owner_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_13_return_function_f__23_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) true) true) (block_12_f_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_12_f_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) true) true) (block_9_return_f_13_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_9_return_f_13_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) true) true) (summary_3_function_f__23_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1))))


(declare-fun |block_14_function_f__23_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(block_14_function_f__23_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_14_function_f__23_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) (and (summary_3_function_f__23_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 owner_4_1 state_3 x_2_2 owner_4_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_2_1 x_2_0)) (= owner_4_1 owner_4_0))) true) true))))))) true) (summary_4_function_f__23_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_3 x_2_2 owner_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (interface_0_C_47_0 this_0 abi_0 crypto_0 state_0 x_2_0 owner_4_0) true) (and (summary_4_function_f__23_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_1 x_2_1 owner_4_1) (= error_0 0))) (interface_0_C_47_0 this_0 abi_0 crypto_0 state_1 x_2_1 owner_4_1))))


(declare-fun |block_15_function_g__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_16_g_45_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(block_15_function_g__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_15_function_g__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_2_1 x_2_0)) (= owner_4_1 owner_4_0))) (and true (= y_25_1 y_25_0))) true)) true) (block_16_g_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1))))


(declare-fun |block_17_return_function_g__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_18_if_header_g_38_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_19_if_true_g_37_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_20_g_45_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_16_g_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (= x_2_2 expr_30_1) (and (=> true (and (>= expr_30_1 0) (<= expr_30_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_1 expr_29_0) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_2_1) (and (=> true true) (and (= expr_29_0 1) (and (and (>= y_25_1 0) (<= y_25_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_18_if_header_g_38_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_2 owner_4_1 y_25_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_18_if_header_g_38_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (= expr_34_1 (> expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 0) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 y_25_1) true)))))) expr_34_1) (block_19_if_true_g_37_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_18_if_header_g_38_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (= expr_34_1 (> expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 0) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 y_25_1) true)))))) (not expr_34_1)) (block_20_g_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1))))


(declare-fun |summary_21_function_f__23_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (summary_3_function_f__23_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_2 x_2_2 owner_4_2) (summary_21_function_f__23_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 state_2 x_2_2 owner_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_19_if_true_g_37_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (summary_21_function_f__23_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 owner_4_1 state_2 x_2_2 owner_4_2) true)) (> error_1 0)) (summary_5_function_g__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_2 x_2_2 owner_4_2 y_25_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_19_if_true_g_37_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (= error_1 0) (and (summary_21_function_f__23_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 owner_4_1 state_2 x_2_2 owner_4_2) true))) true) (block_20_g_45_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_2 x_2_2 owner_4_2 y_25_1))))


(declare-fun |block_22_function_g__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_20_g_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (= expr_42_1 (> expr_40_0 expr_41_0)) (and (=> true true) (and (= expr_41_0 0) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 x_2_1) true)))))) (and (not expr_42_1) (= error_1 1))) (block_22_function_g__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (block_22_function_g__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (summary_5_function_g__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_20_g_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (= error_1 error_0) (and (= expr_42_1 (> expr_40_0 expr_41_0)) (and (=> true true) (and (= expr_41_0 0) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 x_2_1) true))))))) true) (block_17_return_function_g__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_17_return_function_g__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) true) true) (summary_5_function_g__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1))))


(declare-fun |block_23_function_g__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int))
(block_23_function_g__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_23_function_g__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (and (summary_5_function_g__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 owner_4_1 y_25_1 state_3 x_2_2 owner_4_2 y_25_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3827312202)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 228)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 32)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 74)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_2_1 x_2_0)) (= owner_4_1 owner_4_0))) (and true (= y_25_1 y_25_0))) true))))))) true) (summary_6_function_g__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_3 x_2_2 owner_4_2 y_25_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (interface_0_C_47_0 this_0 abi_0 crypto_0 state_0 x_2_0 owner_4_0) true) (and (summary_6_function_g__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (= error_0 0))) (interface_0_C_47_0 this_0 abi_0 crypto_0 state_1 x_2_1 owner_4_1))))


(declare-fun |contract_initializer_24_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_25_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_2_1 x_2_0)) (= owner_4_1 owner_4_0))) (contract_initializer_entry_25_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1))))


(declare-fun |contract_initializer_after_init_26_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (contract_initializer_entry_25_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1) true) true) (contract_initializer_after_init_26_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (contract_initializer_after_init_26_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1) true) true) (contract_initializer_24_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1))))


(declare-fun |implicit_constructor_entry_27_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_2_1 x_2_0)) (= owner_4_1 owner_4_0))) (and (and true (= x_2_1 0)) (= owner_4_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_27_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (implicit_constructor_entry_27_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1) (and (contract_initializer_24_C_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 owner_4_1 x_2_2 owner_4_2) true)) (> error_1 0)) (summary_constructor_2_C_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 owner_4_0 x_2_2 owner_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (implicit_constructor_entry_27_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1) (and (= error_1 0) (and (contract_initializer_24_C_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 owner_4_1 x_2_2 owner_4_2) true))) true) (summary_constructor_2_C_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 owner_4_0 x_2_2 owner_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (summary_constructor_2_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 owner_4_0 x_2_1 owner_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_47_0 this_0 abi_0 crypto_0 state_1 x_2_1 owner_4_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (interface_0_C_47_0 this_0 abi_0 crypto_0 state_0 x_2_0 owner_4_0) true) (and (summary_6_function_g__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 owner_4_0 y_25_0 state_1 x_2_1 owner_4_1 y_25_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_36_1 |tuple()|) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_7_1 Int) (expr_8_0 Int) (expr_9_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (owner_4_0 Int) (owner_4_1 Int) (owner_4_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> error_target_3_0 false)))
(check-sat)