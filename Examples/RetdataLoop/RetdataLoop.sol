// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Minimal proof target for a symbolic loop with low-level calls and
/// a strictly increasing free memory pointer on every successful iteration.
contract RetdataLoop {
    function collect(address[] calldata targets)
        external
        returns (uint256 total)
    {
        for (uint256 i = 0; i < targets.length; i++) {
            (bool ok, bytes memory returndata) = targets[i].call(abi.encodePacked(i));
            require(ok);
            require(returndata.length == 32);
            total += abi.decode(returndata, (uint256));
        }
    }
}
