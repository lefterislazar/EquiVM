// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IProbe {
    function probe(uint256 i) external returns (uint256);
}

contract NestedCaller {
    function run(address target, uint256 count) external returns (uint256) {
        require(count <= 16);
        uint256 last = 0;
        for (uint256 i = 0; i < count; ++i) {
            uint256 value = sample(target, i);
            if (value == 0) continue;
            if (value == 1) break;
            last = value;
        }
        return last;
    }

    function sample(address target, uint256 i) internal returns (uint256) {
        uint256 remaining = gasleft();
        if (remaining < 1000) return 0;
        return IProbe(target).probe(i);
    }
}
