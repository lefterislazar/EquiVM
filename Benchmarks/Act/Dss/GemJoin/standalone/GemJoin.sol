pragma solidity ^0.8.28;
contract GemJoinVat { uint256 public slips; function slip(bytes32,address,int256) external{slips+=1;} }
contract GemJoinStandalone {
 mapping(address=>uint256) public wards; bytes32 public ilk; uint256 public live; GemJoinVat public vat;
 modifier auth(){require(wards[msg.sender]==1);_;}
 constructor(address vat_,bytes32 ilk_){wards[msg.sender]=1;ilk=ilk_;live=1;vat=GemJoinVat(vat_);}
 function rely(address u) external auth{wards[u]=1;} function deny(address u) external auth{wards[u]=0;} function cage() external auth{live=0;}
 function join(address usr,uint256 wad) external{require(live==1&&wad<=uint256(type(int256).max));vat.slip(ilk,usr,int256(wad));}
 function exit(address usr,uint256 wad) external{require(wad<=uint256(type(int256).max));vat.slip(ilk,msg.sender,-int256(wad));}
}
