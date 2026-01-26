import fs from 'fs';

const artifactPath = 'out/ISettlerActions.sol/ISettlerActions.json';
const artifact = JSON.parse(fs.readFileSync(artifactPath, 'utf8'));
const abi = artifact.abi;

function validVip(item) {
    const inputs = item.inputs || [];
    if (inputs.length < 2) {
        return false;
    }
    const recipient = inputs[0];
    const permit = inputs[1];

    // check recipient
    if (recipient.type !== 'address' || recipient.name !== 'recipient') {
        return false;
    }

    // check permit
    return permit.type === 'tuple' && 
        permit.internalType === 'struct ISignatureTransfer.PermitTransferFrom' && 
        (permit.name === 'permit' || permit.name === 'takerPermit');
}

// Find all VIP functions
const malformedVIPs = abi.filter(item =>
    item.type === 'function' &&
    item.name &&
    item.name.endsWith('_VIP')
).filter(item => !validVip(item));

if (malformedVIPs.length > 0) {
    console.error(
        `Malformed VIP functions: ${malformedVIPs.map(item => item.name).join(', ')}`
    );
    process.exit(1);
}
