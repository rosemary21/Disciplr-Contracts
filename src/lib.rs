#![no_std]

use soroban_sdk::{
    contract, contractimpl, contracterror, contracttype, Address, BytesN, Env, Symbol,
};

// ── Constants ─────────────────────────────────────────────────────────────────

/// Maximum allowed vault duration: 365 days (31 536 000 seconds).
///
/// Prevents unbounded lock-up periods and keeps timestamp arithmetic
/// safely within u64 range regardless of the epoch used.
pub const MAX_DURATION: u64 = 365 * 24 * 60 * 60; // 31_536_000 s

/// Maximum stakeable amount in base token units (e.g. USDC micro-units).
///
/// Set to 1 × 10¹⁸ — about 1 trillion USDC at 6 decimal places.
/// This leaves ample headroom while preventing overflow in any fee or
/// percentage arithmetic performed on `amount` downstream.
pub const MAX_AMOUNT: i128 = 1_000_000_000_000_000_000; // 10^18

// ── Error type ────────────────────────────────────────────────────────────────

/// Errors returned by [`DisciplrVault`] contract entry points.
#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u32)]
pub enum VaultError {
    /// `amount` is zero or negative.
    InvalidAmount = 1,
    /// `start_timestamp >= end_timestamp` (timestamps must be strictly ordered).
    InvalidTimestamps = 2,
    /// Vault duration (`end_timestamp - start_timestamp`) exceeds [`MAX_DURATION`].
    DurationTooLong = 3,
    /// `amount` exceeds [`MAX_AMOUNT`].
    AmountTooLarge = 4,
}

// ── Data types ────────────────────────────────────────────────────────────────

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

#[contracttype]
pub struct ProductivityVault {
    pub creator: Address,
    pub amount: i128,
    pub start_timestamp: u64,
    pub end_timestamp: u64,
    pub milestone_hash: BytesN<32>,
    pub verifier: Option<Address>,
    pub success_destination: Address,
    pub failure_destination: Address,
    pub status: VaultStatus,
}

// ── Contract ──────────────────────────────────────────────────────────────────

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC
    /// transfer to this contract.
    ///
    /// # Validation
    ///
    /// | Condition                                           | Error                          |
    /// |-----------------------------------------------------|--------------------------------|
    /// | `amount <= 0`                                       | [`VaultError::InvalidAmount`]  |
    /// | `amount > MAX_AMOUNT`                               | [`VaultError::AmountTooLarge`] |
    /// | `start_timestamp >= end_timestamp`                  | [`VaultError::InvalidTimestamps`] |
    /// | `end_timestamp - start_timestamp > MAX_DURATION`    | [`VaultError::DurationTooLong`]|
    ///
    /// # Errors
    ///
    /// Returns a [`VaultError`] variant on any validation failure.
    pub fn create_vault(
        env: Env,
        creator: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
        milestone_hash: BytesN<32>,
        verifier: Option<Address>,
        success_destination: Address,
        failure_destination: Address,
    ) -> Result<u32, VaultError> {
        creator.require_auth();

        // ── Validate amount ───────────────────────────────────────────────────
        if amount <= 0 {
            return Err(VaultError::InvalidAmount);
        }
        if amount > MAX_AMOUNT {
            return Err(VaultError::AmountTooLarge);
        }

        // ── Validate timestamps ───────────────────────────────────────────────
        if start_timestamp >= end_timestamp {
            return Err(VaultError::InvalidTimestamps);
        }
        // Subtraction is safe: start < end guarantees no underflow.
        if end_timestamp - start_timestamp > MAX_DURATION {
            return Err(VaultError::DurationTooLong);
        }

        // TODO: pull USDC from creator to this contract.
        let vault = ProductivityVault {
            creator: creator.clone(),
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
        };
        let vault_id = 0u32; // placeholder; real impl would allocate id and persist.
        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            vault,
        );
        Ok(vault_id)
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        // TODO: check vault exists, status is Active, caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination, set status Completed
        env.events().publish(
            (Symbol::new(&env, "milestone_validated"), vault_id),
            (),
        );
        true
    }

    /// Release funds to success destination (called after validation or by deadline logic).
    pub fn release_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active, transfer to success_destination, set Completed
        true
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active and past end_timestamp, transfer to failure_destination, set Failed
        true
    }

    /// Cancel vault and return funds to creator (if allowed by rules).
    pub fn cancel_vault(_env: Env, _vault_id: u32) -> bool {
        // TODO: require creator auth, return USDC to creator, set Cancelled
        true
    }

    /// Return current vault state for a given vault id.
    /// Placeholder: returns None; full impl would read from storage.
    pub fn get_vault_state(_env: Env, _vault_id: u32) -> Option<ProductivityVault> {
        None
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use soroban_sdk::{testutils::Address as _, Address, BytesN, Env};

    // Arbitrary but realistic epoch anchors used throughout.
    const T0: u64 = 1_700_000_000; // 2023-11-14 ~22:13 UTC
    const T1: u64 = T0 + 86_400;   // T0 + 1 day

    // ── Helpers ───────────────────────────────────────────────────────────────

    fn zero_hash(env: &Env) -> BytesN<32> {
        BytesN::from_array(env, &[0u8; 32])
    }

    /// Registers the contract and returns a client that borrows `env`.
    fn new_client(env: &Env) -> DisciplrVaultClient<'_> {
        let id = env.register(DisciplrVault, ());
        DisciplrVaultClient::new(env, &id)
    }

    /// Calls `create_vault` expecting success; panics on any error.
    fn call_ok(env: &Env, client: &DisciplrVaultClient, amount: i128, start: u64, end: u64) -> u32 {
        let creator = Address::generate(env);
        let dest = Address::generate(env);
        let no_verifier: Option<Address> = None;
        client
            .try_create_vault(&creator, &amount, &start, &end, &zero_hash(env), &no_verifier, &dest, &dest)
            .expect("expected outer Ok")
            .expect("expected inner Ok")
    }

    /// Calls `create_vault` expecting a [`VaultError`]; panics if it succeeds
    /// or returns a non-contract error.
    fn call_err(env: &Env, client: &DisciplrVaultClient, amount: i128, start: u64, end: u64) -> VaultError {
        let creator = Address::generate(env);
        let dest = Address::generate(env);
        let no_verifier: Option<Address> = None;
        client
            .try_create_vault(&creator, &amount, &start, &end, &zero_hash(env), &no_verifier, &dest, &dest)
            .expect_err("expected Err (outer)")
            .expect("expected Ok(VaultError) (inner)")
    }

    // ── Happy-path tests ──────────────────────────────────────────────────────

    /// A well-formed call must succeed and return vault id 0 (placeholder).
    #[test]
    fn test_valid_vault_returns_id() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(call_ok(&env, &client, 1_000, T0, T1), 0u32);
    }

    /// amount = 1 (minimum positive value) must be accepted.
    #[test]
    fn test_minimum_valid_amount() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        call_ok(&env, &client, 1, T0, T1); // must not panic
    }

    /// amount = MAX_AMOUNT (boundary, inclusive) must be accepted.
    #[test]
    fn test_max_amount_boundary_is_valid() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        call_ok(&env, &client, MAX_AMOUNT, T0, T1);
    }

    /// duration = MAX_DURATION (boundary, inclusive) must be accepted.
    #[test]
    fn test_max_duration_boundary_is_valid() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        call_ok(&env, &client, 1_000, T0, T0 + MAX_DURATION);
    }

    /// Shortest possible valid vault: 1-second window.
    #[test]
    fn test_minimum_duration_one_second() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        call_ok(&env, &client, 1_000, T0, T0 + 1);
    }

    // ── InvalidAmount ─────────────────────────────────────────────────────────

    /// amount = 0 must be rejected.
    #[test]
    fn test_zero_amount_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(
            call_err(&env, &client, 0, T0, T1),
            VaultError::InvalidAmount,
            "zero amount must return InvalidAmount"
        );
    }

    /// amount = -1 must be rejected.
    #[test]
    fn test_negative_one_amount_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(call_err(&env, &client, -1, T0, T1), VaultError::InvalidAmount);
    }

    /// amount = i128::MIN (most negative) must be rejected.
    #[test]
    fn test_i128_min_amount_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(call_err(&env, &client, i128::MIN, T0, T1), VaultError::InvalidAmount);
    }

    // ── AmountTooLarge ────────────────────────────────────────────────────────

    /// amount = MAX_AMOUNT + 1 (just over boundary) must be rejected.
    #[test]
    fn test_amount_one_above_max_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(
            call_err(&env, &client, MAX_AMOUNT + 1, T0, T1),
            VaultError::AmountTooLarge,
            "amount just over MAX_AMOUNT must return AmountTooLarge"
        );
    }

    /// amount = i128::MAX must be rejected.
    #[test]
    fn test_i128_max_amount_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(call_err(&env, &client, i128::MAX, T0, T1), VaultError::AmountTooLarge);
    }

    // ── InvalidTimestamps ─────────────────────────────────────────────────────

    /// start == end must be rejected (zero-duration vault).
    #[test]
    fn test_start_equals_end_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(
            call_err(&env, &client, 1_000, T0, T0),
            VaultError::InvalidTimestamps,
            "start == end must return InvalidTimestamps"
        );
    }

    /// start > end (reversed) must be rejected.
    #[test]
    fn test_start_after_end_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(call_err(&env, &client, 1_000, T1, T0), VaultError::InvalidTimestamps);
    }

    /// start = end + 1 (off-by-one reversal) must be rejected.
    #[test]
    fn test_start_one_past_end_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(call_err(&env, &client, 1_000, T0 + 1, T0), VaultError::InvalidTimestamps);
    }

    // ── DurationTooLong ───────────────────────────────────────────────────────

    /// duration = MAX_DURATION + 1 (just over boundary) must be rejected.
    #[test]
    fn test_duration_one_over_max_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(
            call_err(&env, &client, 1_000, T0, T0 + MAX_DURATION + 1),
            VaultError::DurationTooLong,
            "duration just over MAX_DURATION must return DurationTooLong"
        );
    }

    /// start = 0, end = u64::MAX — extreme overflow candidate — must be rejected.
    #[test]
    fn test_u64_max_end_timestamp_is_rejected() {
        let env = Env::default();
        env.mock_all_auths();
        let client = new_client(&env);
        assert_eq!(call_err(&env, &client, 1_000, 0, u64::MAX), VaultError::DurationTooLong);
    }
}
