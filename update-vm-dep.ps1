# Get the most recent rev for the VM repo
$NewRev = (git ls-remote https://github.com/Barca545/spdr-vm.git HEAD) -match "^\w+" | Out-Null; 
$NewRev = $matches[0];

# Replace the line in Cargo.toml
$Path = '.\Cargo.toml';
# Read all of Cargo.toml into a string and replace the line with a line containing the new rev
$NewContent = (Get-Content -Path $Path -Raw) -replace '(spdr-vm = {git = "https://github.com/Barca545/spdr-vm.git", rev = "\w+"})', "spdr-vm = {git = ""https://github.com/Barca545/spdr-vm.git"", rev = ""$NewRev""}"
Set-Content -Path $Path -Value $NewContent