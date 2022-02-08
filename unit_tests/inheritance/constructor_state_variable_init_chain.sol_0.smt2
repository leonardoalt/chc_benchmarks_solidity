(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_4_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_4_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_4_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |interface_3_B_15_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_4_B_15_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_5_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_4_B_15_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_6_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_7_C_26_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_8_C_26_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_9_C_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_8_C_26_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_10_constructor_14_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_11_constructor_25_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_12_D_45_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_13_D_45_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_14_D_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_13_D_45_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_15_constructor_14_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_16_constructor_25_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_17_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_18_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_19_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_0 x_3_0))) (contract_initializer_entry_19_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_0))))


(declare-fun |contract_initializer_after_init_20_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_entry_19_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 1) true)))) true) (contract_initializer_after_init_20_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_after_init_20_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_18_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_21_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_21_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_21_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_18_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_2_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_21_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= error_1 0) (and (contract_initializer_18_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))) true) (summary_constructor_2_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (summary_constructor_2_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_4_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_22_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_23__13_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_22_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_22_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_23__13_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_24_return_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_23__13_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_11_1) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 expr_10_0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_3_1) (and (=> true true) (and (= expr_10_0 2) true)))))))) true) (block_24_return_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_24_return_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_6_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_25_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_26_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_26_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_27_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_26_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_27_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_27_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_6_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_25_B_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_27_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_6_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_25_B_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |contract_initializer_28_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_29_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (contract_initializer_entry_29_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(declare-fun |contract_initializer_after_init_30_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_29_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 1) true)))) true) (contract_initializer_after_init_30_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_30_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_28_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_31_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_31_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_28_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_5_B_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_31_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_25_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_28_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_5_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_31_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_2 0) (and (contract_initializer_25_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_28_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))) true) (summary_constructor_5_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (summary_constructor_5_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_3_B_15_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_32_constructor_25_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_33__24_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_32_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_32_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_33__24_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_34_return_constructor_25_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_33__24_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_22_1) (and (=> true (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_1 expr_21_0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_3_1) (and (=> true true) (and (= expr_21_0 3) true)))))))) true) (block_34_return_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_34_return_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_11_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_35_C_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_36_C_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_36_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_37_C_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_36_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_37_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_37_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_11_constructor_25_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_35_C_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_37_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_11_constructor_25_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_35_C_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_38_constructor_14_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_39__13_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_38_constructor_14_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_38_constructor_14_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_39__13_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_40_return_constructor_14_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_39__13_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_11_1) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 expr_10_0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_3_1) (and (=> true true) (and (= expr_10_0 2) true)))))))) true) (block_40_return_constructor_14_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_40_return_constructor_14_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_10_constructor_14_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_41_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_42_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_42_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_43_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_42_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_43_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_43_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_10_constructor_14_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_41_B_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_43_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_10_constructor_14_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_41_B_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |contract_initializer_44_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_45_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (contract_initializer_entry_45_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(declare-fun |contract_initializer_after_init_46_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_45_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 1) true)))) true) (contract_initializer_after_init_46_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_46_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_44_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_47_C_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_47_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_47_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_44_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_9_C_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_47_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_41_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_44_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_9_C_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_47_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_35_C_26_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_41_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_44_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))))) (> error_3 0)) (summary_constructor_9_C_26_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_4 x_3_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_47_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_3 0) (and (contract_initializer_35_C_26_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_41_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_44_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))))) true) (summary_constructor_9_C_26_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_4 x_3_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (summary_constructor_9_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_7_C_26_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_48_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_49__43_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(block_48_constructor_44_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_48_constructor_44_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_49__43_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_50_return_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_51_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_49__43_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 3) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_3_1) true)))))) (and (not expr_34_1) (= error_1 1))) (block_51_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (block_51_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_17_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_52_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_49__43_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_40_1 (= expr_38_0 expr_39_0)) (and (=> true true) (and (= expr_39_0 2) (and (=> true (and (>= expr_38_0 0) (<= expr_38_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_0 x_3_1) (and (= error_1 error_0) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 3) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_3_1) true)))))))))))) (and (not expr_40_1) (= error_2 2))) (block_52_constructor_44_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (block_52_constructor_44_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_17_constructor_44_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_49__43_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_2 error_1) (and (= expr_40_1 (= expr_38_0 expr_39_0)) (and (=> true true) (and (= expr_39_0 2) (and (=> true (and (>= expr_38_0 0) (<= expr_38_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_0 x_3_1) (and (= error_1 error_0) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 3) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_3_1) true))))))))))))) true) (block_50_return_constructor_44_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_50_return_constructor_44_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_17_constructor_44_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_53_D_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_54_D_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_54_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_55_D_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_entry_54_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_55_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_after_init_55_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_17_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_53_D_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_after_init_55_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_17_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_53_D_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_56_constructor_25_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_57__24_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(block_56_constructor_25_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_56_constructor_25_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_57__24_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_58_return_constructor_25_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_57__24_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_22_1) (and (=> true (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_1 expr_21_0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_3_1) (and (=> true true) (and (= expr_21_0 3) true)))))))) true) (block_58_return_constructor_25_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_58_return_constructor_25_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_16_constructor_25_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_59_C_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_60_C_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_60_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_61_C_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_entry_60_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_61_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_after_init_61_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_16_constructor_25_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_59_C_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_after_init_61_C_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_16_constructor_25_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_59_C_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_62_constructor_14_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_63__13_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(block_62_constructor_14_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_62_constructor_14_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_63__13_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_64_return_constructor_14_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_63__13_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_11_1) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 expr_10_0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_3_1) (and (=> true true) (and (= expr_10_0 2) true)))))))) true) (block_64_return_constructor_14_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (block_64_return_constructor_14_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_15_constructor_14_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_65_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_66_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_66_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_67_B_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_entry_66_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_67_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_after_init_67_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_15_constructor_14_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_65_B_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_after_init_67_B_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_15_constructor_14_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_65_B_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |contract_initializer_68_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_69_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (contract_initializer_entry_69_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(declare-fun |contract_initializer_after_init_70_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_entry_69_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 1) true)))) true) (contract_initializer_after_init_70_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (contract_initializer_after_init_70_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_68_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_71_D_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_71_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_71_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_68_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_14_D_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_71_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_65_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_68_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_14_D_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_71_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_59_C_26_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_65_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_68_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))))) (> error_3 0)) (summary_constructor_14_D_45_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_4 x_3_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (implicit_constructor_entry_71_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_53_D_45_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 x_3_4 state_5 x_3_5) (and (= error_3 0) (and (contract_initializer_59_C_26_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_65_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_68_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))))))) (> error_4 0)) (summary_constructor_14_D_45_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_5 x_3_5))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (implicit_constructor_entry_71_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_4 0) (and (contract_initializer_53_D_45_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 x_3_4 state_5 x_3_5) (and (= error_3 0) (and (contract_initializer_59_C_26_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_65_B_15_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_68_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))))))) true) (summary_constructor_14_D_45_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_5 x_3_5))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_14_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_12_D_45_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_14_D_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> error_target_3_0 false)))
(check-sat)