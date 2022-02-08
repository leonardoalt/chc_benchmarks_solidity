(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_54_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_54_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_54_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_g__13_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_g__13_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_54_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_g__13_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_54_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_5_function_g2__20_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_6_function_g2__20_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_54_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_6_function_g2__20_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_54_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_7_function_f__31_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_8_function_h__42_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_9_function_i__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_10_function_g__13_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_11_g_12_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_10_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_11_g_12_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_12_return_function_g__13_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_13_function_f__31_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_7_function_f__31_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2) (summary_13_function_f__31_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_g_12_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_13_function_f__31_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_3_function_g__13_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |summary_14_function_h__42_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_4_1 |tuple()|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_8_function_h__42_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3) (summary_14_function_h__42_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_4_1 |tuple()|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_g_12_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_14_function_h__42_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (summary_13_function_f__31_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))) (> error_2 0)) (summary_3_function_g__13_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(declare-fun |summary_15_function_i__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_9_function_i__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4) (summary_15_function_i__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_g_12_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_15_function_i__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4) (and (= error_2 0) (and (summary_14_function_h__42_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (summary_13_function_f__31_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))))) (> error_3 0)) (summary_3_function_g__13_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_g_12_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_3 0) (and (summary_15_function_i__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4) (and (= error_2 0) (and (summary_14_function_h__42_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (summary_13_function_f__31_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))))))) true) (block_12_return_function_g__13_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_return_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_3_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_16_function_g__13_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_16_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_3_function_g__13_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_g__13_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_54_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_54_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_17_function_g2__20_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_18_g2_19_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_17_function_g2__20_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_17_function_g2__20_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_18_g2_19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_19_return_function_g2__20_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_20_function_i__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_9_function_i__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2) (summary_20_function_i__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_18_g2_19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_20_function_i__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_5_function_g2__20_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_18_g2_19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (summary_20_function_i__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (block_19_return_function_g2__20_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_19_return_function_g2__20_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_5_function_g2__20_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_21_function_g2__20_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_21_function_g2__20_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_21_function_g2__20_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_5_function_g2__20_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_1_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_1_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_1_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_1_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and true (= (|msg.sig| tx_0) 1768991012)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 105)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 112)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 169)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 36)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_6_function_g2__20_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_54_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_6_function_g2__20_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_54_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_22_function_f__31_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_23_f_30_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_22_function_f__31_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_22_function_f__31_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_23_f_30_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_24_return_function_f__31_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_23_f_30_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (=> true expr_27_1) (and (= expr_27_1 (= expr_25_1 expr_26_0)) (and (=> true true) (and (= expr_26_0 0) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_25_1 (|msg.value| tx_0)) true))))))) true) (block_24_return_function_f__31_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_24_return_function_f__31_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_7_function_f__31_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_25_function_h__42_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_26_h_41_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_25_function_h__42_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_25_function_h__42_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_26_h_41_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_27_return_function_h__42_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_28_function_h__42_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_26_h_41_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_38_1 (= expr_36_1 expr_37_0)) (and (=> true true) (and (= expr_37_0 0) (and (=> true (and (>= expr_36_1 0) (<= expr_36_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_1 (|msg.value| tx_0)) true)))))) (and (not expr_38_1) (= error_1 2))) (block_28_function_h__42_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_28_function_h__42_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_8_function_h__42_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_26_h_41_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 error_0) (and (= expr_38_1 (= expr_36_1 expr_37_0)) (and (=> true true) (and (= expr_37_0 0) (and (=> true (and (>= expr_36_1 0) (<= expr_36_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_1 (|msg.value| tx_0)) true))))))) true) (block_27_return_function_h__42_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_27_return_function_h__42_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_8_function_h__42_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_29_function_i__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_30_i_52_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_29_function_i__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_29_function_i__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_30_i_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_31_return_function_i__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_32_function_i__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_30_i_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_49_1 (= expr_47_1 expr_48_0)) (and (=> true true) (and (= expr_48_0 0) (and (=> true (and (>= expr_47_1 0) (<= expr_47_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_47_1 (|msg.value| tx_0)) true)))))) (and (not expr_49_1) (= error_1 3))) (block_32_function_i__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_32_function_i__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_9_function_i__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_30_i_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 error_0) (and (= expr_49_1 (= expr_47_1 expr_48_0)) (and (=> true true) (and (= expr_48_0 0) (and (=> true (and (>= expr_47_1 0) (<= expr_47_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_47_1 (|msg.value| tx_0)) true))))))) true) (block_31_return_function_i__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_31_return_function_i__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_9_function_i__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_33_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_34_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_34_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_35_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_34_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_35_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_35_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_33_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_36_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_36_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_36_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_33_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_36_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_33_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_54_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_54_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 2))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_54_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_g__13_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 3))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_54_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_6_function_g2__20_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 3))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 |tuple()|) (expr_17_1 |tuple()|) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Bool) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_47_1 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_4_1 |tuple()|) (expr_7_1 |tuple()|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_5_0 false)))
(check-sat)