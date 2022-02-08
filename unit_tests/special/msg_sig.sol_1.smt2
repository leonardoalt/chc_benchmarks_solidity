(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_72_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_72_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_72_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__24_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_f__24_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_72_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__24_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_72_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_5_function_fi__35_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_6_function_g__49_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_7_function_g__49_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_72_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_7_function_g__49_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_72_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_8_function_gi__60_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_9_function_h__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_10_function_h__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_72_0 error_2 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_2 0) (summary_10_function_h__71_72_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_72_0 error_3 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_11_function_f__24_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_12_f_23_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_11_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_12_f_23_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_13_return_function_f__24_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_14_function_f__24_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_f_23_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_7_1 (= expr_5_1 expr_6_0)) (and (=> true true) (and (= expr_6_0 0) (and (=> true (and (>= expr_5_1 0) (<= expr_5_1 4294967295))) (and (= expr_5_1 (|msg.sig| tx_0)) true)))))) (and (not expr_7_1) (= error_1 1))) (block_14_function_f__24_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_14_function_f__24_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_3_function_f__24_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_15_function_f__24_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_f_23_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_14_1 (= expr_12_1 expr_13_0)) (and (=> true true) (and (= expr_13_0 638722032) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 4294967295))) (and (= expr_12_1 (|msg.sig| tx_0)) (and (= error_1 error_0) (and (= expr_7_1 (= expr_5_1 expr_6_0)) (and (=> true true) (and (= expr_6_0 0) (and (=> true (and (>= expr_5_1 0) (<= expr_5_1 4294967295))) (and (= expr_5_1 (|msg.sig| tx_0)) true)))))))))))) (and (not expr_14_1) (= error_2 2))) (block_15_function_f__24_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_15_function_f__24_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_3_function_f__24_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |summary_16_function_fi__35_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_5_function_fi__35_72_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_16_function_fi__35_72_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_f_23_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_16_function_fi__35_72_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1) (and (= error_2 error_1) (and (= expr_14_1 (= expr_12_1 expr_13_0)) (and (=> true true) (and (= expr_13_0 638722032) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 4294967295))) (and (= expr_12_1 (|msg.sig| tx_0)) (and (= error_1 error_0) (and (= expr_7_1 (= expr_5_1 expr_6_0)) (and (=> true true) (and (= expr_6_0 0) (and (=> true (and (>= expr_5_1 0) (<= expr_5_1 4294967295))) (and (= expr_5_1 (|msg.sig| tx_0)) true)))))))))))))) (> error_3 0)) (summary_3_function_f__24_72_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |summary_17_function_gi__60_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_8_function_gi__60_72_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_17_function_gi__60_72_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_f_23_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_17_function_gi__60_72_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 state_1) (and (= error_3 0) (and (summary_16_function_fi__35_72_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1) (and (= error_2 error_1) (and (= expr_14_1 (= expr_12_1 expr_13_0)) (and (=> true true) (and (= expr_13_0 638722032) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 4294967295))) (and (= expr_12_1 (|msg.sig| tx_0)) (and (= error_1 error_0) (and (= expr_7_1 (= expr_5_1 expr_6_0)) (and (=> true true) (and (= expr_6_0 0) (and (=> true (and (>= expr_5_1 0) (<= expr_5_1 4294967295))) (and (= expr_5_1 (|msg.sig| tx_0)) true)))))))))))))))) (> error_4 0)) (summary_3_function_f__24_72_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_f_23_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_4 0) (and (summary_17_function_gi__60_72_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 state_1) (and (= error_3 0) (and (summary_16_function_fi__35_72_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1) (and (= error_2 error_1) (and (= expr_14_1 (= expr_12_1 expr_13_0)) (and (=> true true) (and (= expr_13_0 638722032) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 4294967295))) (and (= expr_12_1 (|msg.sig| tx_0)) (and (= error_1 error_0) (and (= expr_7_1 (= expr_5_1 expr_6_0)) (and (=> true true) (and (= expr_6_0 0) (and (=> true (and (>= expr_5_1 0) (<= expr_5_1 4294967295))) (and (= expr_5_1 (|msg.sig| tx_0)) true))))))))))))))))) true) (block_13_return_function_f__24_72_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_return_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_3_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_18_function_f__24_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_18_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_18_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_3_function_f__24_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_f__24_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_72_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_72_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_19_function_fi__35_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_20_fi_34_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_19_function_fi__35_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_19_function_fi__35_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_20_fi_34_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_21_return_function_fi__35_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_22_function_fi__35_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_20_fi_34_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_31_1 (= expr_29_1 expr_30_0)) (and (=> true true) (and (= expr_30_0 638722032) (and (=> true (and (>= expr_29_1 0) (<= expr_29_1 4294967295))) (and (= expr_29_1 (|msg.sig| tx_0)) true)))))) (and (not expr_31_1) (= error_1 4))) (block_22_function_fi__35_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_22_function_fi__35_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_5_function_fi__35_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_20_fi_34_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 error_0) (and (= expr_31_1 (= expr_29_1 expr_30_0)) (and (=> true true) (and (= expr_30_0 638722032) (and (=> true (and (>= expr_29_1 0) (<= expr_29_1 4294967295))) (and (= expr_29_1 (|msg.sig| tx_0)) true))))))) true) (block_21_return_function_fi__35_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_21_return_function_fi__35_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_5_function_fi__35_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_23_function_g__49_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_24_g_48_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_23_function_g__49_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_23_function_g__49_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_24_g_48_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_25_return_function_g__49_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_26_function_g__49_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_24_g_48_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_42_1 (= expr_40_1 expr_41_0)) (and (=> true true) (and (= expr_41_0 3793197966) (and (=> true (and (>= expr_40_1 0) (<= expr_40_1 4294967295))) (and (= expr_40_1 (|msg.sig| tx_0)) true)))))) (and (not expr_42_1) (= error_1 5))) (block_26_function_g__49_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_26_function_g__49_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_6_function_g__49_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |summary_27_function_gi__60_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_8_function_gi__60_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_27_function_gi__60_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_24_g_48_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_27_function_gi__60_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_1) (and (= error_1 error_0) (and (= expr_42_1 (= expr_40_1 expr_41_0)) (and (=> true true) (and (= expr_41_0 3793197966) (and (=> true (and (>= expr_40_1 0) (<= expr_40_1 4294967295))) (and (= expr_40_1 (|msg.sig| tx_0)) true)))))))) (> error_2 0)) (summary_6_function_g__49_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_24_g_48_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_2 0) (and (summary_27_function_gi__60_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_1) (and (= error_1 error_0) (and (= expr_42_1 (= expr_40_1 expr_41_0)) (and (=> true true) (and (= expr_41_0 3793197966) (and (=> true (and (>= expr_40_1 0) (<= expr_40_1 4294967295))) (and (= expr_40_1 (|msg.sig| tx_0)) true))))))))) true) (block_25_return_function_g__49_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_25_return_function_g__49_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_6_function_g__49_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_28_function_g__49_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_28_function_g__49_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_28_function_g__49_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_6_function_g__49_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_6_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_6_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_6_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_6_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_7_function_g__49_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_72_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_7_function_g__49_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_72_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_29_function_gi__60_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_30_gi_59_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_29_function_gi__60_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_29_function_gi__60_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_30_gi_59_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_31_return_function_gi__60_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_32_function_gi__60_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_30_gi_59_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_56_1 (= expr_54_1 expr_55_0)) (and (=> true true) (and (= expr_55_0 3793197966) (and (=> true (and (>= expr_54_1 0) (<= expr_54_1 4294967295))) (and (= expr_54_1 (|msg.sig| tx_0)) true)))))) (and (not expr_56_1) (= error_1 7))) (block_32_function_gi__60_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_32_function_gi__60_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_8_function_gi__60_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_30_gi_59_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 error_0) (and (= expr_56_1 (= expr_54_1 expr_55_0)) (and (=> true true) (and (= expr_55_0 3793197966) (and (=> true (and (>= expr_54_1 0) (<= expr_54_1 4294967295))) (and (= expr_54_1 (|msg.sig| tx_0)) true))))))) true) (block_31_return_function_gi__60_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_31_return_function_gi__60_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_8_function_gi__60_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_33_function_h__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_34_h_70_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_33_function_h__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_33_function_h__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_34_h_70_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_35_return_function_h__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_36_function_h__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_34_h_70_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_67_1 (= expr_65_1 expr_66_0)) (and (=> true true) (and (= expr_66_0 3793197966) (and (=> true (and (>= expr_65_1 0) (<= expr_65_1 4294967295))) (and (= expr_65_1 (|msg.sig| tx_0)) true)))))) (and (not expr_67_1) (= error_1 8))) (block_36_function_h__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_36_function_h__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_9_function_h__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_34_h_70_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 error_0) (and (= expr_67_1 (= expr_65_1 expr_66_0)) (and (=> true true) (and (= expr_66_0 3793197966) (and (=> true (and (>= expr_65_1 0) (<= expr_65_1 4294967295))) (and (= expr_65_1 (|msg.sig| tx_0)) true))))))) true) (block_35_return_function_h__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_35_return_function_h__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_9_function_h__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_37_function_h__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_37_function_h__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_37_function_h__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_9_function_h__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_9_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_9_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_9_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_9_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3100234597)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 184)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 201)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 211)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 101)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_10_function_h__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_72_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_10_function_h__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_72_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_38_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_39_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_39_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_40_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_39_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_40_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_40_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_38_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_41_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_41_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_41_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_38_C_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_41_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_38_C_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_72_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_72_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_10_0)))


(declare-fun |error_target_11_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_72_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__24_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 2))) error_target_11_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_1 |tuple()|) (expr_21_1 |tuple()|) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_1 |tuple()|) (expr_54_1 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_5_1 Int) (expr_65_1 Int) (expr_66_0 Int) (expr_67_1 Bool) (expr_6_0 Int) (expr_7_1 Bool) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_11_0 false)))
(check-sat)