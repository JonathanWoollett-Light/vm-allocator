// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Manages system resources that can be allocated to VMs and their devices.
//!
//! # Example
//!
//! Depending on the use case of the VMM, both the `IDAllocator` and the `AddressAllocator`
//! can be used. In the example below we assume that the `IDAllocator` is used for allocating
//! unique identifiers for VM devices. We use the address allocator for allocating MMIO ranges
//! for virtio devices.
//!
//! In the example below we use constants that are typical for the x86 platform, but this has no
//! impact on the code actually working on aarch64.
//!
//! ```rust
//! use std::collections::HashMap;
//! use std::process::id;
//! use vm_allocator::{AddressAllocator, AllocPolicy, Error, IdAllocator, RangeInclusive, Result};
//!
//! const FIRST_ADDR_PAST_32BITS: u64 = 1 << 32;
//! const MEM_32BIT_GAP_SIZE: u64 = 768 << 20;
//! const MMIO_MEM_START: u64 = FIRST_ADDR_PAST_32BITS - MEM_32BIT_GAP_SIZE;
//! const PAGE_SIZE: u64 = 0x1000;
//!
//! struct DeviceManager {
//!     id_allocator: IdAllocator,
//!     mmio_allocator: AddressAllocator,
//!     slots: HashMap<u32, RangeInclusive>,
//! }
//!
//! #[derive(Clone, Copy)]
//! struct DeviceSlot {
//!     id: u32,
//!     mmio_range: RangeInclusive,
//! }
//!
//! impl DeviceManager {
//!     pub fn new() -> Result<Self> {
//!         Ok(DeviceManager {
//!             id_allocator: IdAllocator::new(0, 100)?,
//!             mmio_allocator: AddressAllocator::new(MMIO_MEM_START, MEM_32BIT_GAP_SIZE)?,
//!             slots: HashMap::new(),
//!         })
//!     }
//!
//!     pub fn reserve_device_slot(&mut self) -> Result<DeviceSlot> {
//!         // We're reserving the first available address that is aligned to the page size.
//!         // For each device we reserve one page of addresses.
//!         let mmio_range =
//!             self.mmio_allocator
//!                 .allocate(PAGE_SIZE, PAGE_SIZE, AllocPolicy::FirstMatch)?;
//!         let slot = DeviceSlot {
//!             id: self.id_allocator.allocate_id()?,
//!             mmio_range,
//!         };
//!         self.slots.insert(slot.id, slot.mmio_range);
//!         Ok(slot)
//!     }
//!
//!     // Free the device slot corresponding to the passed device ID.
//!     pub fn free_device_slot(&mut self, id: u32) -> Result<()> {
//!         let mmio_range = self.slots.get(&id).ok_or(Error::NeverAllocated(id))?;
//!         let _ = self.id_allocator.free_id(id)?;
//!         self.mmio_allocator.free(mmio_range)
//!     }
//! }
//!
//! # fn main() {
//! #     let mut dm = DeviceManager::new().unwrap();
//! #    let slot = dm.reserve_device_slot().unwrap();
//! #    dm.free_device_slot(slot.id).unwrap();
//! # }
//! ```

#![deny(missing_docs)]

mod address_allocator;
/// Allocation engine used by address allocator.
mod allocation_engine;
mod id_allocator;
mod space;
pub use space::*;

use std::result;
use thiserror::Error;

use crate::allocation_engine::NodeState;
pub use crate::{address_allocator::AddressAllocator, id_allocator::IdAllocator};

/// Default alignment that can be used for creating a `Constraint`.
pub const DEFAULT_CONSTRAINT_ALIGN: u64 = 4;

/// Error type for IdAllocator usage.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Error)]
pub enum Error {
    /// Management operations on desired resource resulted in overflow.
    #[error("Management operations on desired resource resulted in overflow.")]
    Overflow,
    /// An id that is not part of the specified range was requested to be released.
    #[error("Specified id: {0} is not in the range.")]
    OutOfRange(u32),
    /// An error in space construction.
    #[error("There was an error in constructing the space.")]
    SpaceError(#[from] SpaceError),
    /// An id that was already released was requested to be released.
    #[error("Specified id: {0} is already released.")]
    AlreadyReleased(u32),
    /// An id  that was never allocated was requested to be released.
    #[error("Specified id: {0} was never allocated, can't release it.")]
    NeverAllocated(u32),
    /// The resource we want to use or update is not available.
    #[error("The requested resource is not available.")]
    ResourceNotAvailable,
    /// The range to manage is invalid.
    #[error("The range specified: {0}-{1} is not valid.")]
    InvalidRange(u64, u64),
    /// Alignment value is invalid
    #[error("Alignment value is invalid.")]
    InvalidAlignment,
    /// The range that we try to insert into the interval tree is overlapping
    /// with another node from the tree.
    #[error("Addresses are overlapping.{0:?} intersects with existing {1:?}")]
    Overlap(Space<u64>, Space<u64>),
    /// A node state can be changed just from Free to Allocated, other transitions
    /// are not valid.
    #[error("Invalid state transition for node {0:?} from {1:?} to NodeState::Free")]
    InvalidStateTransition(Space<u64>, NodeState),
    /// Address is unaligned
    #[error("The address is not aligned.")]
    UnalignedAddress,
    /// Management operations on desired resource resulted in underflow.
    #[error("Management operations on desired resource resulted in underflow.")]
    Underflow,
    /// The size of the desired resource is not invalid.
    #[error("The specified size: {0} is not valid.")]
    InvalidSize(u64),
}

/// Wrapper over std::result::Result
pub type Result<T> = result::Result<T, Error>;

/// A resource allocation constraint.
///
/// # Example
///
/// ```rust
/// use vm_allocator::{AllocPolicy, Constraint, Error, IdAllocator, DEFAULT_CONSTRAINT_ALIGN};
///
/// let constraint =
///     Constraint::new(0x4, DEFAULT_CONSTRAINT_ALIGN, AllocPolicy::FirstMatch).unwrap();
/// assert_eq!(constraint.size(), 0x4);
/// assert_eq!(constraint.align(), 0x4);
///
/// // Alignments need to be a power of 2, otherwise an error is returned.
/// assert_eq!(
///     Constraint::new(0x4, 0x3, AllocPolicy::LastMatch).unwrap_err(),
///     Error::InvalidAlignment
/// );
///
/// // When using the ExactMatch policy, the start address must also be aligned, otherwise
/// // an error is returned.
/// assert_eq!(
///     Constraint::new(0x4, 0x4, AllocPolicy::ExactMatch(0x3)).unwrap_err(),
///     Error::UnalignedAddress
/// );
/// ```
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Constraint {
    /// Size to allocate.
    size: u64,
    /// Alignment for the allocated resource.
    align: u64,
    /// Resource allocation policy.
    policy: AllocPolicy,
}

impl Constraint {
    /// Creates a new constraint based on the passed configuration.
    ///
    /// When the `ExactMatch` policy is used, the start address MUST be aligned to the
    /// alignment passed as a parameter.
    ///
    /// # Arguments:
    /// - `size`: size to allocate.
    /// - `align`: alignment to be used for the allocated resources.
    ///            Valid alignments are a power of 2.
    /// - `policy`: allocation policy.
    pub fn new(size: u64, align: u64, policy: AllocPolicy) -> Result<Self> {
        if size == 0 {
            return Err(Error::InvalidSize(size));
        }

        if !align.is_power_of_two() || align == 0 {
            return Err(Error::InvalidAlignment);
        }

        if let AllocPolicy::ExactMatch(start_address) = policy {
            if start_address % align != 0 {
                return Err(Error::UnalignedAddress);
            }
        }

        Ok(Constraint {
            size,
            align,
            policy,
        })
    }

    /// Returns the alignment constraint.
    pub fn align(self) -> u64 {
        self.align
    }

    /// Returns the size constraint.
    pub fn size(self) -> u64 {
        self.size
    }
}

/// Policy for resource allocation.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum AllocPolicy {
    /// Allocate the first matched entry.
    FirstMatch,
    /// Allocate first matched entry from the end of the range.
    LastMatch,
    /// Allocate a memory slot starting with the specified address
    /// if it is available.
    ExactMatch(u64),
}

impl Default for AllocPolicy {
    fn default() -> Self {
        AllocPolicy::FirstMatch
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constraint_getter() {
        let bad_constraint = Constraint::new(0x1000, 0x1000, AllocPolicy::ExactMatch(0xC));
        assert_eq!(bad_constraint.unwrap_err(), Error::UnalignedAddress);
        let constraint = Constraint::new(0x1000, 0x1000, AllocPolicy::default()).unwrap();
        assert_eq!(constraint.align(), 0x1000);
        assert_eq!(constraint.size(), 0x1000);
    }
}
