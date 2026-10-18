// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

// Storage pointers placed at arbitrary slots with inline assembly. Used to exercise arrays
// whose storage straddles the end of the address space (LostStorageArrayWriteOnSlotOverflow).
contract SlotPointers {
  struct Box { uint256[4] w; }
  struct PBox { uint8[40] w; }

  function d_box_at(uint256 slot) external { Box storage x; assembly { x.slot := slot } delete x.w; }
  function w_box_at(uint256 slot, uint256[4] memory v) external { Box storage x; assembly { x.slot := slot } x.w = v; }
  function d_pbox_at(uint256 slot) external { PBox storage x; assembly { x.slot := slot } delete x.w; }
}
