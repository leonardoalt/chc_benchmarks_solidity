(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_9_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_A_9_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_A_9_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_4_function_f__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (r_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_A_9_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__8_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_1))) (nondet_interface_1_A_9_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_5_B_25_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_6_B_25_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_7_B_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (r_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_6_B_25_0 error_1 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_8_function_f__8_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_9_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_10_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (r_15_1 Int) (r_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_6_B_25_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_10_function_f__24_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_15_1))) (nondet_interface_6_B_25_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_11_C_41_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_12_C_41_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_13_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (r_15_1 Int) (r_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_2 0) (nondet_interface_12_C_41_0 error_2 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_14_function_f__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_15_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_16_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (r_15_1 Int) (r_31_1 Int) (r_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_12_C_41_0 error_2 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_2 0) (summary_16_function_f__40_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_31_1))) (nondet_interface_12_C_41_0 error_3 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_17_D_75_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_18_D_75_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_19_D_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (r_15_1 Int) (r_31_1 Int) (r_3_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_3 0) (nondet_interface_18_D_75_0 error_3 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_20_function_f__8_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_21_function_f__24_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_22_function_f__40_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_23_function_f__74_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_24_function_f__74_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (r_15_1 Int) (r_31_1 Int) (r_3_1 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_18_D_75_0 error_3 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_3 0) (summary_24_function_f__74_75_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_51_1))) (nondet_interface_18_D_75_0 error_4 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_25_function_f__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_26_f_7_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_25_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_25_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_26_f_7_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1))))


(declare-fun |block_27_return_function_f__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_26_f_7_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (= r_3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1) (and (= r_3_1 0) true))))) true) (block_27_return_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2))))


(declare-fun |block_28_return_ghost_f_6_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_28_return_ghost_f_6_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2) (and (= r_3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1) (and (= r_3_1 0) true))))) true) (block_27_return_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_27_return_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) true) true) (summary_3_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1))))


(declare-fun |block_29_function_f__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_29_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_29_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (summary_3_function_f__8_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 r_3_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_f__8_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 r_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_A_9_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (= error_0 0))) (interface_0_A_9_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_30_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_31_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_31_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_32_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_31_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_32_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_32_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_30_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_33_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_33_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_33_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_30_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_33_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_30_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_31_1 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_51_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_9_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_34_function_f__8_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_35_f_7_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_34_function_f__8_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_34_function_f__8_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_35_f_7_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1))))


(declare-fun |block_36_return_function_f__8_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_35_f_7_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (= r_3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1) (and (= r_3_1 0) true))))) true) (block_36_return_function_f__8_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2))))


(declare-fun |block_37_return_ghost_f_6_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_37_return_ghost_f_6_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2) (and (= r_3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1) (and (= r_3_1 0) true))))) true) (block_36_return_function_f__8_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_36_return_function_f__8_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) true) true) (summary_8_function_f__8_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1))))


(declare-fun |block_38_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_39_f_23_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_38_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_38_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_39_f_23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1))))


(declare-fun |block_40_return_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_41_function_f__8_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_8_function_f__8_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_3_2) (summary_41_function_f__8_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_39_f_23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) (and (summary_41_function_f__8_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_15_1 0) true))) (> error_1 0)) (summary_9_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_39_f_23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) (and (= r_15_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 (+ expr_19_0 expr_20_0)) (and (=> true true) (and (= expr_20_0 2) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 r_3_2) (and (= error_1 0) (and (summary_41_function_f__8_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_15_1 0) true))))))))))) true) (block_40_return_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_2))))


(declare-fun |block_42_return_ghost_f_22_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_42_return_ghost_f_22_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_2) (and (= r_15_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 (+ expr_19_0 expr_20_0)) (and (=> true true) (and (= expr_20_0 2) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 r_3_2) (and (= error_1 0) (and (summary_41_function_f__8_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_15_1 0) true))))))))))) true) (block_40_return_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_40_return_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) true) true) (summary_9_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1))))


(declare-fun |block_43_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_43_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_43_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) (and (summary_9_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 r_15_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_1_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_1_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_1_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_1_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_10_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 r_15_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_5_B_25_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_10_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) (= error_0 0))) (interface_5_B_25_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_44_B_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_45_B_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_45_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_46_B_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_45_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_46_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_46_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_44_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_47_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_48_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_48_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_49_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_48_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_49_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_49_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_47_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_50_B_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_50_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_50_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_47_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_7_B_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_50_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_44_B_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_47_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))) (> error_2 0)) (summary_constructor_7_B_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_50_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_2 0) (and (contract_initializer_44_B_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_47_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))))) true) (summary_constructor_7_B_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_7_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_B_25_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_51_function_f__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_52_f_7_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_51_function_f__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_51_function_f__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_52_f_7_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1))))


(declare-fun |block_53_return_function_f__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_52_f_7_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (= r_3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1) (and (= r_3_1 0) true))))) true) (block_53_return_function_f__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2))))


(declare-fun |block_54_return_ghost_f_6_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_54_return_ghost_f_6_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2) (and (= r_3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1) (and (= r_3_1 0) true))))) true) (block_53_return_function_f__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_53_return_function_f__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) true) true) (summary_14_function_f__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1))))


(declare-fun |block_55_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_56_f_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_55_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_55_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_56_f_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1))))


(declare-fun |block_57_return_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_58_function_f__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_14_function_f__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_3_2) (summary_58_function_f__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_56_f_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) (and (summary_58_function_f__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_31_1 0) true))) (> error_1 0)) (summary_15_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_56_f_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) (and (= r_31_2 expr_37_1) (and (=> true (and (>= expr_37_1 0) (<= expr_37_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_37_1 (+ expr_35_0 expr_36_0)) (and (=> true true) (and (= expr_36_0 4) (and (=> true (and (>= expr_35_0 0) (<= expr_35_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_0 r_3_2) (and (= error_1 0) (and (summary_58_function_f__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_31_1 0) true))))))))))) true) (block_57_return_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_2))))


(declare-fun |block_59_return_ghost_f_38_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_59_return_ghost_f_38_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_2) (and (= r_31_2 expr_37_1) (and (=> true (and (>= expr_37_1 0) (<= expr_37_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_37_1 (+ expr_35_0 expr_36_0)) (and (=> true true) (and (= expr_36_0 4) (and (=> true (and (>= expr_35_0 0) (<= expr_35_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_0 r_3_2) (and (= error_1 0) (and (summary_58_function_f__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_31_1 0) true))))))))))) true) (block_57_return_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_57_return_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) true) true) (summary_15_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1))))


(declare-fun |block_60_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_60_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_60_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) (and (summary_15_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 r_31_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_16_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 r_31_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_11_C_41_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_16_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) (= error_0 0))) (interface_11_C_41_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_61_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_62_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_62_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_63_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_62_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_63_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_63_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_61_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_64_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_65_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_65_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_66_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_65_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_66_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_66_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_64_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_67_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_67_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_67_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_64_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_13_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_67_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_61_C_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_64_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))) (> error_2 0)) (summary_constructor_13_C_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_67_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_2 0) (and (contract_initializer_61_C_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_64_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))))) true) (summary_constructor_13_C_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_13_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_11_C_41_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_68_function_f__8_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_69_f_7_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_68_function_f__8_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_68_function_f__8_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_69_f_7_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1))))


(declare-fun |block_70_return_function_f__8_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_69_f_7_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) (and (= r_3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1) (and (= r_3_1 0) true))))) true) (block_70_return_function_f__8_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2))))


(declare-fun |block_71_return_ghost_f_6_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_71_return_ghost_f_6_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2) (and (= r_3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1) (and (= r_3_1 0) true))))) true) (block_70_return_function_f__8_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_70_return_function_f__8_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1) true) true) (summary_20_function_f__8_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_3_1))))


(declare-fun |block_72_function_f__24_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_73_f_23_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_72_function_f__24_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_72_function_f__24_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_73_f_23_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1))))


(declare-fun |block_74_return_function_f__24_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_75_function_f__8_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_20_function_f__8_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_3_2) (summary_75_function_f__8_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_73_f_23_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) (and (summary_75_function_f__8_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_15_1 0) true))) (> error_1 0)) (summary_21_function_f__24_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_73_f_23_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) (and (= r_15_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 (+ expr_19_0 expr_20_0)) (and (=> true true) (and (= expr_20_0 2) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 r_3_2) (and (= error_1 0) (and (summary_75_function_f__8_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_15_1 0) true))))))))))) true) (block_74_return_function_f__24_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_2))))


(declare-fun |block_76_return_ghost_f_22_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_76_return_ghost_f_22_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_2) (and (= r_15_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 (+ expr_19_0 expr_20_0)) (and (=> true true) (and (= expr_20_0 2) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 r_3_2) (and (= error_1 0) (and (summary_75_function_f__8_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_3_2) (and (= r_15_1 0) true))))))))))) true) (block_74_return_function_f__24_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_74_return_function_f__24_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1) true) true) (summary_21_function_f__24_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_15_1))))


(declare-fun |block_77_function_f__40_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_78_f_39_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_77_function_f__40_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_77_function_f__40_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_78_f_39_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1))))


(declare-fun |block_79_return_function_f__40_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_80_function_f__24_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_21_function_f__24_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_2) (summary_80_function_f__24_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_15_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_78_f_39_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) (and (summary_80_function_f__24_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_15_2) (and (= r_31_1 0) true))) (> error_1 0)) (summary_22_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_78_f_39_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) (and (= r_31_2 expr_37_1) (and (=> true (and (>= expr_37_1 0) (<= expr_37_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_37_1 (+ expr_35_0 expr_36_0)) (and (=> true true) (and (= expr_36_0 4) (and (=> true (and (>= expr_35_0 0) (<= expr_35_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_0 r_15_2) (and (= error_1 0) (and (summary_80_function_f__24_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_15_2) (and (= r_31_1 0) true))))))))))) true) (block_79_return_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_2))))


(declare-fun |block_81_return_ghost_f_38_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_81_return_ghost_f_38_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_2) (and (= r_31_2 expr_37_1) (and (=> true (and (>= expr_37_1 0) (<= expr_37_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_37_1 (+ expr_35_0 expr_36_0)) (and (=> true true) (and (= expr_36_0 4) (and (=> true (and (>= expr_35_0 0) (<= expr_35_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_0 r_15_2) (and (= error_1 0) (and (summary_80_function_f__24_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_15_2) (and (= r_31_1 0) true))))))))))) true) (block_79_return_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_79_return_function_f__40_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1) true) true) (summary_22_function_f__40_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_31_1))))


(declare-fun |block_82_function_f__74_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_83_f_73_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_82_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_82_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_83_f_73_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1))))


(declare-fun |block_84_return_function_f__74_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_85_function_f__40_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_22_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_2) (summary_85_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_31_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_83_f_73_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (and (summary_85_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_31_2) (and (= r_51_1 0) true))) (> error_1 0)) (summary_23_function_f__74_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_51_1))))


(declare-fun |block_86_function_f__74_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_83_f_73_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (and (= expr_64_1 (= expr_62_0 expr_63_0)) (and (=> true true) (and (= expr_63_0 15) (and (=> true (and (>= expr_62_0 0) (<= expr_62_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_62_0 r_51_2) (and (= r_51_2 expr_59_1) (and (=> true (and (>= expr_59_1 0) (<= expr_59_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_59_1 expr_58_1) (and (=> true (and (>= expr_53_0 0) (<= expr_53_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_53_0 r_51_1) (and (=> true (and (>= expr_58_1 0) (<= expr_58_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_58_1 (+ expr_56_0 expr_57_0)) (and (=> true true) (and (= expr_57_0 8) (and (=> true (and (>= expr_56_0 0) (<= expr_56_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_56_0 r_31_2) (and (= error_1 0) (and (summary_85_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_31_2) (and (= r_51_1 0) true)))))))))))))))))))) (and (not expr_64_1) (= error_2 3))) (block_86_function_f__74_75_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_51_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_86_function_f__74_75_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_51_2) (summary_23_function_f__74_75_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_51_2))))


(declare-fun |block_87_function_f__74_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_83_f_73_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (and (= expr_70_1 (= expr_68_0 expr_69_0)) (and (=> true true) (and (= expr_69_0 13) (and (=> true (and (>= expr_68_0 0) (<= expr_68_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_68_0 r_51_2) (and (= error_2 error_1) (and (= expr_64_1 (= expr_62_0 expr_63_0)) (and (=> true true) (and (= expr_63_0 15) (and (=> true (and (>= expr_62_0 0) (<= expr_62_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_62_0 r_51_2) (and (= r_51_2 expr_59_1) (and (=> true (and (>= expr_59_1 0) (<= expr_59_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_59_1 expr_58_1) (and (=> true (and (>= expr_53_0 0) (<= expr_53_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_53_0 r_51_1) (and (=> true (and (>= expr_58_1 0) (<= expr_58_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_58_1 (+ expr_56_0 expr_57_0)) (and (=> true true) (and (= expr_57_0 8) (and (=> true (and (>= expr_56_0 0) (<= expr_56_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_56_0 r_31_2) (and (= error_1 0) (and (summary_85_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_31_2) (and (= r_51_1 0) true)))))))))))))))))))))))))) (and (not expr_70_1) (= error_3 4))) (block_87_function_f__74_75_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_51_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_87_function_f__74_75_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_51_2) (summary_23_function_f__74_75_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_51_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_83_f_73_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (and (= error_3 error_2) (and (= expr_70_1 (= expr_68_0 expr_69_0)) (and (=> true true) (and (= expr_69_0 13) (and (=> true (and (>= expr_68_0 0) (<= expr_68_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_68_0 r_51_2) (and (= error_2 error_1) (and (= expr_64_1 (= expr_62_0 expr_63_0)) (and (=> true true) (and (= expr_63_0 15) (and (=> true (and (>= expr_62_0 0) (<= expr_62_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_62_0 r_51_2) (and (= r_51_2 expr_59_1) (and (=> true (and (>= expr_59_1 0) (<= expr_59_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_59_1 expr_58_1) (and (=> true (and (>= expr_53_0 0) (<= expr_53_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_53_0 r_51_1) (and (=> true (and (>= expr_58_1 0) (<= expr_58_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_58_1 (+ expr_56_0 expr_57_0)) (and (=> true true) (and (= expr_57_0 8) (and (=> true (and (>= expr_56_0 0) (<= expr_56_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_56_0 r_31_2) (and (= error_1 0) (and (summary_85_function_f__40_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 r_31_2) (and (= r_51_1 0) true))))))))))))))))))))))))))) true) (block_84_return_function_f__74_75_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_2 r_51_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_84_return_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) true) true) (summary_23_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1))))


(declare-fun |block_88_function_f__74_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_88_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_88_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (and (summary_23_function_f__74_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 r_51_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_5_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_5_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_5_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_5_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_24_function_f__74_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 r_51_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_17_D_75_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_24_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (= error_0 0))) (interface_17_D_75_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_89_D_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_90_D_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_90_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_91_D_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_90_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_91_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_91_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_89_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_92_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_93_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_93_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_94_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_93_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_94_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_94_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_92_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_95_B_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_96_B_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_96_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_97_B_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_96_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_97_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_97_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_95_B_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_98_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_99_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_99_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_100_A_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_99_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_100_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_100_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_98_A_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_101_D_75_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_101_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_101_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_98_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_19_D_75_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_101_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_95_B_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_98_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))) (> error_2 0)) (summary_constructor_19_D_75_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_101_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_92_C_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4) (and (= error_2 0) (and (contract_initializer_95_B_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_98_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))))) (> error_3 0)) (summary_constructor_19_D_75_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_101_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_89_D_75_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5) (and (= error_3 0) (and (contract_initializer_92_C_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4) (and (= error_2 0) (and (contract_initializer_95_B_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_98_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))))))) (> error_4 0)) (summary_constructor_19_D_75_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_101_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_4 0) (and (contract_initializer_89_D_75_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5) (and (= error_3 0) (and (contract_initializer_92_C_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4) (and (= error_2 0) (and (contract_initializer_95_B_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_98_A_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))))))))) true) (summary_constructor_19_D_75_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_19_D_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_17_D_75_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_17_D_75_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_24_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (= error_0 3))) error_target_6_0)))


(declare-fun |error_target_7_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_17_D_75_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_24_function_f__74_75_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 r_51_1) (= error_0 4))) error_target_7_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Int) (expr_53_0 Int) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_59_1 Int) (expr_5_0 Int) (expr_62_0 Int) (expr_63_0 Int) (expr_64_1 Bool) (expr_68_0 Int) (expr_69_0 Int) (expr_70_1 Bool) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_5_0 Int) (r_15_0 Int) (r_15_1 Int) (r_15_2 Int) (r_15_3 Int) (r_15_4 Int) (r_15_5 Int) (r_31_0 Int) (r_31_1 Int) (r_31_2 Int) (r_31_3 Int) (r_31_4 Int) (r_31_5 Int) (r_3_0 Int) (r_3_1 Int) (r_3_2 Int) (r_3_3 Int) (r_3_4 Int) (r_51_0 Int) (r_51_1 Int) (r_51_2 Int) (r_51_3 Int) (r_51_4 Int) (r_51_5 Int) (r_51_6 Int) (r_51_7 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_7_0 false)))
(check-sat)