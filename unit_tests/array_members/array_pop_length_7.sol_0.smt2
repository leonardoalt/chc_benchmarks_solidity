(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|uint_array_tuple| 0)) (((|uint_array_tuple| (|uint_array_tuple_accessor_array| (Array Int Int)) (|uint_array_tuple_accessor_length| Int)))))
(declare-fun |interface_0_C_18_0| (Int |abi_type| |crypto_type| |state_type| |uint_array_tuple| ) Bool)
(declare-fun |nondet_interface_1_C_18_0| (Int Int |abi_type| |crypto_type| |state_type| |uint_array_tuple| |state_type| |uint_array_tuple| ) Bool)
(declare-fun |summary_constructor_2_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |uint_array_tuple| |uint_array_tuple| ) Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_18_0 error_0 this_0 abi_0 crypto_0 state_0 a_3_length_pair_0 state_0 a_3_length_pair_0))))


(declare-fun |summary_3_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |uint_array_tuple| |state_type| |uint_array_tuple| ) Bool)
(declare-fun |summary_4_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |uint_array_tuple| |state_type| |uint_array_tuple| ) Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_18_0 error_0 this_0 abi_0 crypto_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1) true) (and (= error_0 0) (summary_4_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_3_length_pair_1 state_2 a_3_length_pair_2))) (nondet_interface_1_C_18_0 error_1 this_0 abi_0 crypto_0 state_0 a_3_length_pair_0 state_2 a_3_length_pair_2))))


(declare-fun |block_5_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |uint_array_tuple| |state_type| |uint_array_tuple| ) Bool)
(declare-fun |block_6_f_16_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |uint_array_tuple| |state_type| |uint_array_tuple| ) Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_5_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1)))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_3_length_pair_1 a_3_length_pair_0))) true) true)) true) (block_6_f_16_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1))))


(declare-fun |block_7_return_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |uint_array_tuple| |state_type| |uint_array_tuple| ) Bool)
(declare-fun |block_8_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |uint_array_tuple| |state_type| |uint_array_tuple| ) Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_16_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1) (and (= expr_11_length_pair_0 a_3_length_pair_2) (and (= a_3_length_pair_2 expr_6_length_pair_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 0) (and (= (|uint_array_tuple_accessor_length| expr_6_length_pair_1) (+ (|uint_array_tuple_accessor_length| expr_6_length_pair_0) 1)) (and (= (|uint_array_tuple_accessor_array| expr_6_length_pair_1) (store (|uint_array_tuple_accessor_array| expr_6_length_pair_0) (|uint_array_tuple_accessor_length| expr_6_length_pair_0) 0)) (and (< (+ (|uint_array_tuple_accessor_length| expr_6_length_pair_0) 1) (- 115792089237316195423570985008687907853269984665640564039457584007913129639935 1)) (and (>= (|uint_array_tuple_accessor_length| expr_6_length_pair_0) 0) (and (= expr_6_length_pair_0 a_3_length_pair_1) true)))))))))) (and (<= (|uint_array_tuple_accessor_length| expr_11_length_pair_0) 0) (= error_1 1))) (block_8_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_2))))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_8_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_2) (summary_3_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_2))))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_16_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1) (and (= a_3_length_pair_3 expr_11_length_pair_1) (and (= (|uint_array_tuple_accessor_length| expr_11_length_pair_1) (ite (> (|uint_array_tuple_accessor_length| expr_11_length_pair_0) 0) (- (|uint_array_tuple_accessor_length| expr_11_length_pair_0) 1) 0)) (and (= (|uint_array_tuple_accessor_array| expr_11_length_pair_1) (|uint_array_tuple_accessor_array| expr_11_length_pair_0)) (and (= error_1 error_0) (and (= expr_11_length_pair_0 a_3_length_pair_2) (and (= a_3_length_pair_2 expr_6_length_pair_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 0) (and (= (|uint_array_tuple_accessor_length| expr_6_length_pair_1) (+ (|uint_array_tuple_accessor_length| expr_6_length_pair_0) 1)) (and (= (|uint_array_tuple_accessor_array| expr_6_length_pair_1) (store (|uint_array_tuple_accessor_array| expr_6_length_pair_0) (|uint_array_tuple_accessor_length| expr_6_length_pair_0) 0)) (and (< (+ (|uint_array_tuple_accessor_length| expr_6_length_pair_0) 1) (- 115792089237316195423570985008687907853269984665640564039457584007913129639935 1)) (and (>= (|uint_array_tuple_accessor_length| expr_6_length_pair_0) 0) (and (= expr_6_length_pair_0 a_3_length_pair_1) true)))))))))))))) true) (block_7_return_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_3))))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_return_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1) true) true) (summary_3_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1))))


(declare-fun |block_9_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |uint_array_tuple| |state_type| |uint_array_tuple| ) Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_9_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1)))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1) (and (summary_3_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 a_3_length_pair_1 state_3 a_3_length_pair_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_3_length_pair_1 a_3_length_pair_0))) true) true))))))) true) (summary_4_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_3 a_3_length_pair_2))))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_18_0 this_0 abi_0 crypto_0 state_0 a_3_length_pair_0) true) (and (summary_4_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1) (= error_0 0))) (interface_0_C_18_0 this_0 abi_0 crypto_0 state_1 a_3_length_pair_1))))


(declare-fun |contract_initializer_10_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |uint_array_tuple| |uint_array_tuple| ) Bool)
(declare-fun |contract_initializer_entry_11_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |uint_array_tuple| |uint_array_tuple| ) Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_3_length_pair_1 a_3_length_pair_0))) (contract_initializer_entry_11_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1))))


(declare-fun |contract_initializer_after_init_12_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |uint_array_tuple| |uint_array_tuple| ) Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_11_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1) true) true) (contract_initializer_after_init_12_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1))))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_12_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1) true) true) (contract_initializer_10_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1))))


(declare-fun |implicit_constructor_entry_13_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |uint_array_tuple| |uint_array_tuple| ) Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_3_length_pair_1 a_3_length_pair_0))) (and true (= a_3_length_pair_1 (|uint_array_tuple| ((as const (Array Int Int)) 0) 0)))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_13_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1))))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_13_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1) (and (contract_initializer_10_C_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 a_3_length_pair_1 a_3_length_pair_2) true)) (> error_1 0)) (summary_constructor_2_C_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_3_length_pair_0 a_3_length_pair_2))))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_13_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1) (and (= error_1 0) (and (contract_initializer_10_C_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 a_3_length_pair_1 a_3_length_pair_2) true))) true) (summary_constructor_2_C_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_3_length_pair_0 a_3_length_pair_2))))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_3_length_pair_0 a_3_length_pair_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_18_0 this_0 abi_0 crypto_0 state_1 a_3_length_pair_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_18_0 this_0 abi_0 crypto_0 state_0 a_3_length_pair_0) true) (and (summary_4_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_3_length_pair_0 state_1 a_3_length_pair_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (a_3_length_pair_0 |uint_array_tuple|) (a_3_length_pair_1 |uint_array_tuple|) (a_3_length_pair_2 |uint_array_tuple|) (a_3_length_pair_3 |uint_array_tuple|) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_length_pair_0 |uint_array_tuple|) (expr_11_length_pair_1 |uint_array_tuple|) (expr_6_length_pair_0 |uint_array_tuple|) (expr_6_length_pair_1 |uint_array_tuple|) (expr_9_1 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_3_0 false)))
(check-sat)