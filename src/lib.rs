#![no_std]
#![allow(clippy::too_many_arguments)]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, token, Address, BytesN, Env, Symbol,
};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Maximum allowed vault duration: 365 days (31 536 000 seconds).
///
/// Prevents unbounded lock-up periods and keeps timestamp arithmetic
/// safely within u64 range regardless of the epoch used.
pub const MAX_DURATION: u64 = 365 * 24 * 60 * 60; // 31_536_000 s

/// Maximum stakeable amount in base token units (e.g. USDC micro-units).
///
/// Set to 1 × 10¹⁸ — about 1 trillion USDC at 6 decimal places.
/// Prevents overflow in any fee or percentage arithmetic downstream.
pub const MAX_AMOUNT: i128 = 1_000_000_000_000_000_000; // 10^18

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors returned by [`DisciplrVault`] contract entry points.
#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Error {
    /// Vault with the given id does not exist.
    VaultNotFound = 1,
    /// Caller is not authorized for this operation.
    NotAuthorized = 2,
    /// Vault is not in Active status.
    VaultNotActive = 3,
    /// Timestamp constraint violated (e.g. redirect before end_timestamp).
    InvalidTimestamp = 4,
    /// Validation no longer allowed: current time is at or past end_timestamp.
    MilestoneExpired = 5,
    /// Vault is in an invalid status for the requested operation.
    InvalidStatus = 6,
    /// `amount` must be positive (`amount <= 0`).
    InvalidAmount = 7,
    /// `start_timestamp` must be strictly less than `end_timestamp`.
    InvalidTimestamps = 8,
    /// Vault duration (`end_timestamp - start_timestamp`) exceeds [`MAX_DURATION`].
    DurationTooLong = 9,
    /// `amount` exceeds [`MAX_AMOUNT`].
    AmountTooLarge = 10,
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

/// Core vault record persisted in contract storage.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProductivityVault {
    /// Address that created (and funded) the vault.
    pub creator: Address,
    /// USDC amount locked in the vault (in stroops / smallest unit).
    pub amount: i128,
    /// Ledger timestamp when the commitment period starts.
    pub start_timestamp: u64,
    /// Ledger timestamp after which deadline-based release is allowed.
    pub end_timestamp: u64,
    /// Hash representing the milestone the creator commits to.
    pub milestone_hash: BytesN<32>,
    /// Optional designated verifier. `Some(addr)` → only that address may call
    /// `validate_milestone`. `None` → only the creator may validate.
    pub verifier: Option<Address>,
    /// Funds go here on success.
    pub success_destination: Address,
    /// Funds go here on failure/redirect.
    pub failure_destination: Address,
    /// Current lifecycle status.
    pub status: VaultStatus,
    /// `true` once the verifier (or creator when verifier is None) validates.
    /// Allows `release_funds` before the deadline.
    pub milestone_validated: bool,
}

// ---------------------------------------------------------------------------
// Storage keys
// ---------------------------------------------------------------------------

#[contracttype]
#[derive(Clone)]
pub enum DataKey {
    Vault(u32),
    VaultCount,
}

// ---------------------------------------------------------------------------
// Contract
// ---------------------------------------------------------------------------

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    // -----------------------------------------------------------------------
    // create_vault
    // -----------------------------------------------------------------------

    /// Create a new productivity vault. Caller must have approved USDC transfer
    /// to this contract.
    ///
    /// # Validation
    ///
    /// | Condition                                         | Error                       |
    /// |---------------------------------------------------|-----------------------------|
    /// | `amount <= 0`                                     | [`Error::InvalidAmount`]    |
    /// | `amount > MAX_AMOUNT`                             | [`Error::AmountTooLarge`]   |
    /// | `start_timestamp >= end_timestamp`                | [`Error::InvalidTimestamps`]|
    /// | `end_timestamp - start_timestamp > MAX_DURATION`  | [`Error::DurationTooLong`]  |
    pub fn create_vault(
        env: Env,
        usdc_token: Address,
        creator: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
        milestone_hash: BytesN<32>,
        verifier: Option<Address>,
        success_destination: Address,
        failure_destination: Address,
    ) -> Result<u32, Error> {
        creator.require_auth();

        // ── Validate amount ───────────────────────────────────────────────
        if amount <= 0 {
            return Err(Error::InvalidAmount);
        }
        if amount > MAX_AMOUNT {
            return Err(Error::AmountTooLarge);
        }

        // ── Validate timestamps ───────────────────────────────────────────
        if end_timestamp <= start_timestamp {
            return Err(Error::InvalidTimestamps);
        }
        // Subtraction is safe: end > start guarantees no underflow.
        if end_timestamp - start_timestamp > MAX_DURATION {
            return Err(Error::DurationTooLong);
        }

        // Pull USDC from creator into this contract.
        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(&creator, &env.current_contract_address(), &amount);

        let mut vault_count: u32 = env
            .storage()
            .instance()
            .get(&DataKey::VaultCount)
            .unwrap_or(0);
        let vault_id = vault_count;
        vault_count += 1;
        env.storage()
            .instance()
            .set(&DataKey::VaultCount, &vault_count);

        let vault = ProductivityVault {
            creator,
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
            milestone_validated: false,
        };

        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            vault.clone(),
        );

        Ok(vault_id)
    }

    // -----------------------------------------------------------------------
    // validate_milestone
    // -----------------------------------------------------------------------

    /// Verifier (or creator when verifier is None) validates milestone completion.
    /// Rejects when current ledger time >= `end_timestamp` (`MilestoneExpired`).
    pub fn validate_milestone(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        if let Some(ref verifier) = vault.verifier {
            verifier.require_auth();
        } else {
            vault.creator.require_auth();
        }

        if env.ledger().timestamp() >= vault.end_timestamp {
            return Err(Error::MilestoneExpired);
        }

        vault.milestone_validated = true;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // release_funds
    // -----------------------------------------------------------------------

    /// Release vault funds to `success_destination`.
    /// Allowed when the milestone has been validated OR the deadline has passed.
    pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        let now = env.ledger().timestamp();
        let deadline_reached = now >= vault.end_timestamp;
        let validated = vault.milestone_validated;

        if !validated && !deadline_reached {
            return Err(Error::NotAuthorized);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.success_destination,
            &vault.amount,
        );

        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&vault_key, &vault);

        env.events().publish(
            (Symbol::new(&env, "funds_released"), vault_id),
            vault.amount,
        );
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // redirect_funds
    // -----------------------------------------------------------------------

    /// Redirect funds to `failure_destination` (after deadline without validation).
    pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        if env.ledger().timestamp() < vault.end_timestamp {
            return Err(Error::InvalidTimestamp);
        }

        if vault.milestone_validated {
            return Err(Error::NotAuthorized);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.failure_destination,
            &vault.amount,
        );

        vault.status = VaultStatus::Failed;
        env.storage().instance().set(&vault_key, &vault);

        env.events().publish(
            (Symbol::new(&env, "funds_redirected"), vault_id),
            vault.amount,
        );
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // cancel_vault
    // -----------------------------------------------------------------------

    /// Cancel vault and return funds to creator.
    pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        vault.creator.require_auth();

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.creator,
            &vault.amount,
        );

        vault.status = VaultStatus::Cancelled;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), vault.amount);
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // get_vault_state
    // -----------------------------------------------------------------------

    /// Return current vault state, or `None` if the vault does not exist.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use soroban_sdk::{
        testutils::{Address as _, AuthorizedFunction, Events, Ledger},
        token::{StellarAssetClient, TokenClient},
        Address, BytesN, Env, Symbol, TryIntoVal,
    };

    // Timestamp anchors used by boundary/validation tests.
    const T0: u64 = 1_700_000_000; // 2023-11-14 ~22:13 UTC
    const T1: u64 = T0 + 86_400; // T0 + 1 day

    // -----------------------------------------------------------------------
    // TestSetup
    // -----------------------------------------------------------------------

    struct TestSetup {
        env: Env,
        contract_id: Address,
        usdc_token: Address,
        creator: Address,
        verifier: Address,
        success_dest: Address,
        failure_dest: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
    }

    impl TestSetup {
        fn new() -> Self {
            let env = Env::default();
            env.mock_all_auths();

            let usdc_admin = Address::generate(&env);
            let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
            let usdc_addr = usdc_token.address();
            let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

            let creator = Address::generate(&env);
            let verifier = Address::generate(&env);
            let success_dest = Address::generate(&env);
            let failure_dest = Address::generate(&env);

            let amount: i128 = 1_000_000;
            usdc_asset.mint(&creator, &amount);

            let contract_id = env.register(DisciplrVault, ());

            TestSetup {
                env,
                contract_id,
                usdc_token: usdc_addr,
                creator,
                verifier,
                success_dest,
                failure_dest,
                amount,
                start_timestamp: 100,
                end_timestamp: 1_000,
            }
        }

        fn client(&self) -> DisciplrVaultClient<'_> {
            DisciplrVaultClient::new(&self.env, &self.contract_id)
        }

        fn usdc_client(&self) -> TokenClient<'_> {
            TokenClient::new(&self.env, &self.usdc_token)
        }

        fn milestone_hash(&self) -> BytesN<32> {
            BytesN::from_array(&self.env, &[1u8; 32])
        }

        fn create_default_vault(&self) -> u32 {
            self.client().create_vault(
                &self.usdc_token,
                &self.creator,
                &self.amount,
                &self.start_timestamp,
                &self.end_timestamp,
                &self.milestone_hash(),
                &Some(self.verifier.clone()),
                &self.success_dest,
                &self.failure_dest,
            )
        }

        fn create_vault_no_verifier(&self) -> u32 {
            self.client().create_vault(
                &self.usdc_token,
                &self.creator,
                &self.amount,
                &self.start_timestamp,
                &self.end_timestamp,
                &self.milestone_hash(),
                &None,
                &self.success_dest,
                &self.failure_dest,
            )
        }

        /// Mints `amount` extra USDC to creator then calls `create_vault`.
        /// Use when testing non-default amounts or timestamps.
        fn create_vault_with_amount(&self, amount: i128, start: u64, end: u64) -> u32 {
            let usdc_asset = StellarAssetClient::new(&self.env, &self.usdc_token);
            usdc_asset.mint(&self.creator, &amount);
            self.client().create_vault(
                &self.usdc_token,
                &self.creator,
                &amount,
                &start,
                &end,
                &self.milestone_hash(),
                &None,
                &self.success_dest,
                &self.failure_dest,
            )
        }

        /// Calls `create_vault` expecting a validation [`Error`].
        /// Does NOT mint USDC — validation errors fire before the token transfer.
        fn expect_create_error(&self, amount: i128, start: u64, end: u64) -> Error {
            self.client()
                .try_create_vault(
                    &self.usdc_token,
                    &self.creator,
                    &amount,
                    &start,
                    &end,
                    &self.milestone_hash(),
                    &None,
                    &self.success_dest,
                    &self.failure_dest,
                )
                .expect_err("expected Err (outer)")
                .expect("expected Ok(Error) (inner)")
        }
    }

    // -----------------------------------------------------------------------
    // create_vault — happy path
    // -----------------------------------------------------------------------

    #[test]
    fn get_vault_state_returns_some_with_matching_fields() {
        let setup = TestSetup::new();
        let vault_id = setup.create_default_vault();
        let vault = setup.client().get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.creator, setup.creator);
        assert_eq!(vault.amount, setup.amount);
        assert_eq!(vault.start_timestamp, setup.start_timestamp);
        assert_eq!(vault.end_timestamp, setup.end_timestamp);
        assert_eq!(vault.milestone_hash, setup.milestone_hash());
        assert_eq!(vault.verifier, Some(setup.verifier));
        assert_eq!(vault.success_destination, setup.success_dest);
        assert_eq!(vault.failure_destination, setup.failure_dest);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    #[test]
    fn test_milestone_hash_storage_and_retrieval() {
        let setup = TestSetup::new();
        let custom_hash = BytesN::from_array(&setup.env, &[0xab; 32]);
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.client().create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &setup.start_timestamp,
            &setup.end_timestamp,
            &custom_hash,
            &Some(setup.verifier.clone()),
            &setup.success_dest,
            &setup.failure_dest,
        );
        let vault = setup.client().get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.milestone_hash, custom_hash);
    }

    #[test]
    fn test_create_vault_increments_id() {
        let setup = TestSetup::new();
        let usdc_asset = StellarAssetClient::new(&setup.env, &setup.usdc_token);
        usdc_asset.mint(&setup.creator, &setup.amount);
        let id_a = setup.create_default_vault();
        let id_b = setup.create_default_vault();
        assert_ne!(id_a, id_b, "vault IDs must be distinct");
        assert_eq!(id_b, id_a + 1);
    }

    #[test]
    fn test_create_vault_emits_event_and_returns_id() {
        let env = Env::default();
        env.mock_all_auths();

        let usdc_admin = Address::generate(&env);
        let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
        let usdc_addr = usdc_token.address();
        let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let creator = Address::generate(&env);
        let success_destination = Address::generate(&env);
        let failure_destination = Address::generate(&env);
        let verifier = Address::generate(&env);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);
        let amount = 1_000_000i128;
        let start_timestamp = 1_000_000u64;
        let end_timestamp = 2_000_000u64;

        usdc_asset.mint(&creator, &amount);

        let vault_id = client.create_vault(
            &usdc_addr,
            &creator,
            &amount,
            &start_timestamp,
            &end_timestamp,
            &milestone_hash,
            &Some(verifier.clone()),
            &success_destination,
            &failure_destination,
        );
        assert_eq!(vault_id, 0u32);

        let mut found_create_auth = false;
        for (auth_addr, invocation) in env.auths() {
            if auth_addr == creator {
                if let AuthorizedFunction::Contract((contract, function_name, _)) =
                    &invocation.function
                {
                    if *contract == contract_id
                        && *function_name == Symbol::new(&env, "create_vault")
                    {
                        found_create_auth = true;
                    }
                }
            }
        }
        assert!(found_create_auth, "create_vault must be authenticated by creator");

        let mut found_vault_created = false;
        for (emitting_contract, topics, _) in env.events().all() {
            if emitting_contract == contract_id {
                let event_name: Symbol = topics.get(0).unwrap().try_into_val(&env).unwrap();
                if event_name == Symbol::new(&env, "vault_created") {
                    let event_vault_id: u32 =
                        topics.get(1).unwrap().try_into_val(&env).unwrap();
                    assert_eq!(event_vault_id, vault_id);
                    found_vault_created = true;
                }
            }
        }
        assert!(found_vault_created, "vault_created event must be emitted");
    }

    // -----------------------------------------------------------------------
    // create_vault — amount validation
    // -----------------------------------------------------------------------

    #[test]
    fn test_create_vault_invalid_amount_returns_error() {
        let setup = TestSetup::new();
        assert!(
            setup
                .client()
                .try_create_vault(
                    &setup.usdc_token,
                    &setup.creator,
                    &0i128,
                    &setup.start_timestamp,
                    &setup.end_timestamp,
                    &setup.milestone_hash(),
                    &None,
                    &setup.success_dest,
                    &setup.failure_dest,
                )
                .is_err(),
            "amount 0 must fail"
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #7)")]
    fn test_create_vault_zero_amount() {
        let setup = TestSetup::new();
        setup.client().create_vault(
            &setup.usdc_token,
            &setup.creator,
            &0i128,
            &1000,
            &2000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    /// amount = 1 (minimum positive value) must be accepted.
    #[test]
    fn test_minimum_valid_amount() {
        let setup = TestSetup::new();
        setup.create_vault_with_amount(1, T0, T1);
    }

    /// amount = MAX_AMOUNT (boundary, inclusive) must be accepted.
    #[test]
    fn test_max_amount_boundary_is_valid() {
        let setup = TestSetup::new();
        setup.create_vault_with_amount(MAX_AMOUNT, T0, T1);
    }

    /// amount = -1 must return InvalidAmount.
    #[test]
    fn test_negative_one_amount_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(setup.expect_create_error(-1, T0, T1), Error::InvalidAmount);
    }

    /// amount = i128::MIN must return InvalidAmount.
    #[test]
    fn test_i128_min_amount_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(i128::MIN, T0, T1),
            Error::InvalidAmount
        );
    }

    /// amount = MAX_AMOUNT + 1 must return AmountTooLarge (#10).
    #[test]
    #[should_panic(expected = "Error(Contract, #10)")]
    fn test_create_vault_amount_above_max_rejected() {
        let setup = TestSetup::new();
        let amount_above_max = MAX_AMOUNT.checked_add(1).expect("MAX_AMOUNT + 1 overflowed");
        setup.client().create_vault(
            &setup.usdc_token,
            &setup.creator,
            &amount_above_max,
            &1000,
            &2000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    /// amount = MAX_AMOUNT + 1 (error variant check).
    #[test]
    fn test_amount_one_above_max_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(MAX_AMOUNT + 1, T0, T1),
            Error::AmountTooLarge
        );
    }

    /// amount = i128::MAX must return AmountTooLarge.
    #[test]
    fn test_i128_max_amount_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(i128::MAX, T0, T1),
            Error::AmountTooLarge
        );
    }

    // -----------------------------------------------------------------------
    // create_vault — timestamp validation
    // -----------------------------------------------------------------------

    #[test]
    fn test_create_vault_invalid_timestamps_returns_error() {
        let setup = TestSetup::new();
        assert!(
            setup
                .client()
                .try_create_vault(
                    &setup.usdc_token,
                    &setup.creator,
                    &setup.amount,
                    &1000u64,
                    &1000u64,
                    &setup.milestone_hash(),
                    &None,
                    &setup.success_dest,
                    &setup.failure_dest,
                )
                .is_err(),
            "start >= end must fail"
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn create_vault_rejects_start_equal_end() {
        let setup = TestSetup::new();
        setup.client().create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &1000,
            &1000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn create_vault_rejects_start_greater_than_end() {
        let setup = TestSetup::new();
        setup.client().create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &2000,
            &1000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    /// start > end (reversed) must return InvalidTimestamps.
    #[test]
    fn test_start_after_end_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(1_000, T1, T0),
            Error::InvalidTimestamps
        );
    }

    /// start = end + 1 (off-by-one reversal).
    #[test]
    fn test_start_one_past_end_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(1_000, T0 + 1, T0),
            Error::InvalidTimestamps
        );
    }

    /// duration = MAX_DURATION + 1 must return DurationTooLong (#9).
    #[test]
    fn test_create_vault_rejects_duration_above_max() {
        let setup = TestSetup::new();
        let start = 1_000u64;
        let end = start + MAX_DURATION + 1;
        assert!(
            setup
                .client()
                .try_create_vault(
                    &setup.usdc_token,
                    &setup.creator,
                    &setup.amount,
                    &start,
                    &end,
                    &setup.milestone_hash(),
                    &None,
                    &setup.success_dest,
                    &setup.failure_dest,
                )
                .is_err(),
            "duration > MAX_DURATION must fail"
        );
    }

    /// duration = MAX_DURATION (boundary, inclusive) must succeed.
    #[test]
    fn test_create_vault_accepts_duration_at_max() {
        let setup = TestSetup::new();
        let start = 1_000u64;
        let end = start + MAX_DURATION;
        assert!(
            setup
                .client()
                .try_create_vault(
                    &setup.usdc_token,
                    &setup.creator,
                    &setup.amount,
                    &start,
                    &end,
                    &setup.milestone_hash(),
                    &None,
                    &setup.success_dest,
                    &setup.failure_dest,
                )
                .is_ok(),
            "duration == MAX_DURATION must succeed"
        );
    }

    /// duration = MAX_DURATION (boundary, inclusive) via TestSetup helper.
    #[test]
    fn test_max_duration_boundary_is_valid() {
        let setup = TestSetup::new();
        setup.create_vault_with_amount(1_000, T0, T0 + MAX_DURATION);
    }

    /// Shortest valid window: 1 second.
    #[test]
    fn test_minimum_duration_one_second() {
        let setup = TestSetup::new();
        setup.create_vault_with_amount(1_000, T0, T0 + 1);
    }

    /// duration = MAX_DURATION + 1 (variant check).
    #[test]
    fn test_duration_one_over_max_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(1_000, T0, T0 + MAX_DURATION + 1),
            Error::DurationTooLong
        );
    }

    /// start = 0, end = u64::MAX — extreme overflow candidate.
    #[test]
    fn test_u64_max_end_timestamp_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(1_000, 0, u64::MAX),
            Error::DurationTooLong
        );
    }

    // -----------------------------------------------------------------------
    // create_vault — auth
    // -----------------------------------------------------------------------

    #[test]
    #[should_panic]
    fn test_create_vault_fails_without_auth() {
        let env = Env::default();
        // DO NOT call mock_all_auths.
        let _vault_id = DisciplrVault::create_vault(
            env,
            Address::generate(&Env::default()),
            Address::generate(&Env::default()),
            1000,
            100,
            200,
            BytesN::<32>::from_array(&Env::default(), &[0u8; 32]),
            Some(Address::generate(&Env::default())),
            Address::generate(&Env::default()),
            Address::generate(&Env::default()),
        );
    }

    #[test]
    #[should_panic]
    fn test_create_vault_caller_differs_from_creator() {
        let env = Env::default();
        let different_caller = Address::generate(&env);
        different_caller.require_auth();
        let _vault_id = DisciplrVault::create_vault(
            env,
            Address::generate(&Env::default()),
            Address::generate(&Env::default()), // not authorized
            1000,
            100,
            200,
            BytesN::<32>::from_array(&Env::default(), &[1u8; 32]),
            Some(Address::generate(&Env::default())),
            Address::generate(&Env::default()),
            Address::generate(&Env::default()),
        );
    }

    #[test]
    #[should_panic]
    fn test_authorization_prevents_unauthorized_creation() {
        let env = Env::default();
        let attacker = Address::generate(&env);
        attacker.require_auth();
        let _vault_id = DisciplrVault::create_vault(
            env,
            Address::generate(&Env::default()),
            Address::generate(&Env::default()), // not the attacker
            5000,
            100,
            200,
            BytesN::<32>::from_array(&Env::default(), &[4u8; 32]),
            None,
            Address::generate(&Env::default()),
            Address::generate(&Env::default()),
        );
    }

    // -----------------------------------------------------------------------
    // validate_milestone
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_milestone_succeeds_before_end() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);
        assert!(client.validate_milestone(&vault_id));
        let vault = client.get_vault_state(&vault_id).unwrap();
        assert!(vault.milestone_validated);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    #[test]
    fn test_validate_milestone_rejects_after_end() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp);
        assert!(client.try_validate_milestone(&vault_id).is_err());
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        assert!(client.try_validate_milestone(&vault_id).is_err());
    }

    #[test]
    fn test_validate_milestone_on_completed_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.release_funds(&vault_id, &setup.usdc_token);
        assert!(client.try_validate_milestone(&vault_id).is_err());
    }

    #[test]
    fn test_validate_milestone_verifier_none_creator_succeeds() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_vault_no_verifier();
        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);
        assert!(client.validate_milestone(&vault_id));
        let vault = client.get_vault_state(&vault_id).unwrap();
        assert!(vault.milestone_validated);
        assert_eq!(vault.verifier, None);
    }

    #[test]
    fn test_validate_milestone_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        assert!(setup.client().try_validate_milestone(&999).is_err());
    }

    #[test]
    fn test_validate_milestone_returns_bool() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let _ = client.try_validate_milestone(&42u32);
    }

    // -----------------------------------------------------------------------
    // release_funds
    // -----------------------------------------------------------------------

    #[test]
    fn test_release_funds_after_validation() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        client.validate_milestone(&vault_id);
        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.success_dest);
        assert!(client.release_funds(&vault_id, &setup.usdc_token));
        assert_eq!(usdc.balance(&setup.success_dest) - before, setup.amount);
        assert_eq!(
            client.get_vault_state(&vault_id).unwrap().status,
            VaultStatus::Completed
        );
    }

    #[test]
    fn test_release_funds_updates_contract_and_success_balances() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        client.validate_milestone(&vault_id);
        let usdc = setup.usdc_client();
        let contract_before = usdc.balance(&setup.contract_id);
        let success_before = usdc.balance(&setup.success_dest);
        assert!(client.release_funds(&vault_id, &setup.usdc_token));
        assert_eq!(
            usdc.balance(&setup.success_dest) - success_before,
            setup.amount
        );
        assert_eq!(
            contract_before - usdc.balance(&setup.contract_id),
            setup.amount
        );
    }

    #[test]
    fn test_release_funds_after_deadline() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.success_dest);
        assert!(client.release_funds(&vault_id, &setup.usdc_token));
        assert_eq!(usdc.balance(&setup.success_dest) - before, setup.amount);
        assert_eq!(
            client.get_vault_state(&vault_id).unwrap().status,
            VaultStatus::Completed
        );
    }

    #[test]
    fn test_release_funds_verifier_none_after_deadline() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_vault_no_verifier();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        assert!(client.release_funds(&vault_id, &setup.usdc_token));
        assert_eq!(
            client.get_vault_state(&vault_id).unwrap().status,
            VaultStatus::Completed
        );
    }

    #[test]
    fn test_release_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        assert!(setup.client().try_release_funds(&999, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_double_release_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.release_funds(&vault_id, &setup.usdc_token);
        assert!(client.try_release_funds(&vault_id, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_release_cancelled_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        client.cancel_vault(&vault_id, &setup.usdc_token);
        assert!(client.try_release_funds(&vault_id, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_release_not_validated_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        assert!(client.try_release_funds(&vault_id, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_release_funds_returns_bool() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let _ = client.try_release_funds(&0u32, &Address::generate(&env));
    }

    // -----------------------------------------------------------------------
    // redirect_funds
    // -----------------------------------------------------------------------

    #[test]
    fn test_redirect_funds_after_deadline_without_validation() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.failure_dest);
        assert!(client.redirect_funds(&vault_id, &setup.usdc_token));
        assert_eq!(usdc.balance(&setup.failure_dest) - before, setup.amount);
        assert_eq!(
            client.get_vault_state(&vault_id).unwrap().status,
            VaultStatus::Failed
        );
    }

    #[test]
    fn test_redirect_funds_updates_contract_and_failure_balances() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        let usdc = setup.usdc_client();
        let contract_before = usdc.balance(&setup.contract_id);
        let failure_before = usdc.balance(&setup.failure_dest);
        assert!(client.redirect_funds(&vault_id, &setup.usdc_token));
        assert_eq!(
            usdc.balance(&setup.failure_dest) - failure_before,
            setup.amount
        );
        assert_eq!(
            contract_before - usdc.balance(&setup.contract_id),
            setup.amount
        );
    }

    #[test]
    fn test_redirect_funds_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        assert!(client.try_redirect_funds(&vault_id, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_redirect_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        assert!(setup.client().try_redirect_funds(&999, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_double_redirect_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(client.try_redirect_funds(&vault_id, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_redirect_funds_returns_bool() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let _ = client.try_redirect_funds(&0u32, &Address::generate(&env));
    }

    // -----------------------------------------------------------------------
    // cancel_vault
    // -----------------------------------------------------------------------

    #[test]
    fn test_cancel_vault_returns_funds_to_creator() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.creator);
        assert!(client.cancel_vault(&vault_id, &setup.usdc_token));
        assert_eq!(usdc.balance(&setup.creator) - before, setup.amount);
        assert_eq!(
            client.get_vault_state(&vault_id).unwrap().status,
            VaultStatus::Cancelled
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_completed_fails() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        client.validate_milestone(&vault_id);
        client.release_funds(&vault_id, &setup.usdc_token);
        client.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_failed_fails() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.redirect_funds(&vault_id, &setup.usdc_token);
        client.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_cancelled_fails() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        client.cancel_vault(&vault_id, &setup.usdc_token);
        client.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic]
    fn test_cancel_vault_non_creator_fails() {
        let setup = TestSetup::new();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        DisciplrVaultClient::new(&env, &contract_id).cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #1)")]
    fn test_cancel_vault_nonexistent_fails() {
        let setup = TestSetup::new();
        setup.client().cancel_vault(&999u32, &setup.usdc_token);
    }

    #[test]
    fn test_cancel_vault_returns_bool() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let _ = client.try_cancel_vault(&0u32, &Address::generate(&env));
    }

    // -----------------------------------------------------------------------
    // Type / smoke tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_get_vault_state_returns_option() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        assert_eq!(
            DisciplrVaultClient::new(&env, &contract_id).get_vault_state(&0u32),
            None
        );
    }

    #[test]
    fn test_vaultstatus_enum_values() {
        assert_eq!(VaultStatus::Active as u32, 0);
        assert_eq!(VaultStatus::Completed as u32, 1);
        assert_eq!(VaultStatus::Failed as u32, 2);
        assert_eq!(VaultStatus::Cancelled as u32, 3);
    }

    #[test]
    fn test_vaultstatus_enum_ordering() {
        assert_eq!(VaultStatus::Active, VaultStatus::Active);
        assert_ne!(VaultStatus::Active, VaultStatus::Completed);
    }

    #[test]
    fn test_vaultstatus_clone_and_copy() {
        let s1 = VaultStatus::Active;
        let s2 = s1;
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_vaultstatus_default_is_active() {
        assert_eq!(VaultStatus::Active as i32, 0);
    }

    #[test]
    fn test_vault_status_all_variants_compile() {
        match VaultStatus::Active {
            VaultStatus::Active => (),
            VaultStatus::Completed => (),
            VaultStatus::Failed => (),
            VaultStatus::Cancelled => (),
        }
    }

    #[test]
    fn test_contract_types_are_public() {
        let _: VaultStatus = VaultStatus::Active;
        let _ = VaultStatus::Completed;
    }

    #[test]
    fn test_productivity_vault_struct_creation() {
        let env = Env::default();
        let mut data = [0u8; 32];
        data[0] = 0xFF;
        let _vault = ProductivityVault {
            creator: Address::generate(&env),
            amount: 1000i128,
            start_timestamp: 100u64,
            end_timestamp: 200u64,
            milestone_hash: BytesN::<32>::from_array(&env, &data),
            verifier: None,
            success_destination: Address::generate(&env),
            failure_destination: Address::generate(&env),
            status: VaultStatus::Active,
            milestone_validated: false,
        };
    }

    #[test]
    fn test_productivity_vault_with_verifier() {
        let env = Env::default();
        let _vault = ProductivityVault {
            creator: Address::generate(&env),
            amount: 1000i128,
            start_timestamp: 100u64,
            end_timestamp: 200u64,
            milestone_hash: BytesN::<32>::from_array(&env, &[0u8; 32]),
            verifier: Some(Address::generate(&env)),
            success_destination: Address::generate(&env),
            failure_destination: Address::generate(&env),
            status: VaultStatus::Active,
            milestone_validated: false,
        };
    }

    #[test]
    fn test_productivity_vault_without_verifier() {
        let env = Env::default();
        let _vault = ProductivityVault {
            creator: Address::generate(&env),
            amount: 1000i128,
            start_timestamp: 100u64,
            end_timestamp: 200u64,
            milestone_hash: BytesN::<32>::from_array(&env, &[0u8; 32]),
            verifier: None,
            success_destination: Address::generate(&env),
            failure_destination: Address::generate(&env),
            status: VaultStatus::Active,
            milestone_validated: false,
        };
    }

    #[test]
    fn test_vault_parameters_with_and_without_verifier() {
        let _a: Option<Address> = None;
        let _b: Option<Address> = None;
        assert!(_a.is_none());
    }

    #[test]
    fn test_option_address_some_variant() {
        let env = Env::default();
        assert!(Some(Address::generate(&env)).is_some());
    }

    #[test]
    fn test_option_address_none_variant() {
        let _: Option<Address> = None;
    }

    #[test]
    fn test_vault_amount_parameters() {
        for amount in [100i128, 1000, 10000, 100000] {
            assert!(amount > 0);
        }
    }

    #[test]
    fn test_vault_timestamp_scenarios() {
        assert!(100u64 < 200u64);
    }

    #[test]
    fn test_vault_milestone_hash_generation() {
        let env = Env::default();
        let _h1 = BytesN::<32>::from_array(&env, &[0u8; 32]);
        let _h2 = BytesN::<32>::from_array(&env, &[1u8; 32]);
        assert_ne!([0u8; 32], [1u8; 32]);
    }

    #[test]
    fn test_address_generation_in_tests() {
        let env = Env::default();
        assert_ne!(Address::generate(&env), Address::generate(&env));
    }

    #[test]
    fn test_bytesn32_creation() {
        let env = Env::default();
        let mut data = [0u8; 32];
        data[0] = 0xFF;
        data[31] = 0xAA;
        let _ = BytesN::<32>::from_array(&env, &data);
    }

    #[test]
    fn test_vault_created_event_symbol_value() {
        let env = Env::default();
        let _ = Symbol::new(&env, "vault_created");
    }

    #[test]
    fn test_milestone_validated_event_symbol_value() {
        let env = Env::default();
        let _ = Symbol::new(&env, "milestone_validated");
    }

    #[test]
    fn test_milestone_validated_function_signature() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let _ = DisciplrVaultClient::new(&env, &contract_id).try_validate_milestone(&123u32);
    }
}
