pragma solidity ^0.8.28;
contract FlopperVat { uint256 public sucked; function suck(address,address,uint256 rad) external{sucked+=rad;} }
contract FlopperGem { uint256 public minted; function mint(address,uint256 wad) external{minted+=wad;} }
contract FlopperStandalone {
 mapping(address=>uint256) public wards; mapping(uint256=>uint256) public bid; mapping(uint256=>uint256) public lot; mapping(uint256=>address) public guy;
 uint256 public kicks; uint256 public live; address public vow; FlopperVat public vat; FlopperGem public gem;
 modifier auth(){require(wards[msg.sender]==1);_;}
 constructor(address vat_,address gem_){require(vat_!=gem_);wards[msg.sender]=1;live=1;vat=FlopperVat(vat_);gem=FlopperGem(gem_);}
 function rely(address u) external auth{wards[u]=1;} function deny(address u) external auth{wards[u]=0;}
 function kick(address,uint256,uint256) external auth returns(uint256 id){require(live==1);id=++kicks;}
 function deal(uint256 id) external{require(live==1&&guy[id]!=address(0));gem.mint(guy[id],lot[id]);}
 function cage() external auth{live=0;vow=msg.sender;}
 function yank(uint256 id) external{require(live==0&&guy[id]!=address(0));vat.suck(vow,guy[id],bid[id]);}
}
