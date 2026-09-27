pragma solidity ^0.8.28;
contract ExponentialDecreaseStandalone { mapping(address=>uint256) public wards; uint256 public cut; modifier auth(){require(wards[msg.sender]==1);_;} constructor(){wards[msg.sender]=1;} function rely(address u) external auth{wards[u]=1;} function deny(address u) external auth{wards[u]=0;} function fileCut(uint256 x) external auth{require(x<=10**27);cut=x;} }
