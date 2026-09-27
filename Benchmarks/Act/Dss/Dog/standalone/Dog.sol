pragma solidity ^0.8.28;

contract DogVat { uint256 public grabs; function grab(bytes32,address,address,address,int256,int256) external { grabs += 1; } }
contract DogVow { uint256 public fessed; function fess(uint256 rad) external { fessed += rad; } }
contract DogClipper { uint256 public kicks; function kick(uint256,uint256,address,address) external returns(uint256 id){id=++kicks;} }

contract DogStandalone {
    mapping(address=>uint256) public wards;
    mapping(bytes32=>uint256) public ilkChop;
    mapping(bytes32=>uint256) public ilkHole;
    mapping(bytes32=>uint256) public ilkDirt;
    uint256 public live; uint256 public Hole; uint256 public Dirt;
    DogVat public vat; DogVow public vow; DogClipper public clip;
    uint256 constant WAD=10**18;
    modifier auth(){require(wards[msg.sender]==1);_;}
    constructor(address vat_,address vow_,address clip_){require(vat_!=vow_&&vat_!=clip_&&vow_!=clip_);wards[msg.sender]=1;live=1;vat=DogVat(vat_);vow=DogVow(vow_);clip=DogClipper(clip_);}
    function rely(address u) external auth{wards[u]=1;}
    function deny(address u) external auth{wards[u]=0;}
    function fileHole(uint256 x) external auth{Hole=x;}
    function fileIlk(bytes32 ilk,uint256 chop,uint256 hole) external auth{require(chop>=WAD);ilkChop[ilk]=chop;ilkHole[ilk]=hole;}
    function digs(bytes32 ilk,uint256 rad) external auth{Dirt-=rad;ilkDirt[ilk]-=rad;}
    function cage() external auth{live=0;}
    function bark(bytes32 ilk,address urn,address kpr) external returns(uint256 id){
        require(live==1&&ilkChop[ilk]>=WAD&&Hole>Dirt&&ilkHole[ilk]>ilkDirt[ilk]);
        vat.grab(ilk,urn,address(clip),address(vow),-int256(1),-int256(1));vow.fess(1);
        Dirt+=1;ilkDirt[ilk]+=1;id=clip.kick(1,1,urn,kpr);
    }
}
