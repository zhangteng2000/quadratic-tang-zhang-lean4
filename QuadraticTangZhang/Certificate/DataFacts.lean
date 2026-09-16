import QuadraticTangZhang.Certificate.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace QuadraticTangZhang.CertificateData

theorem record_count : records.length=6593 := by decide +kernel
theorem block_count : blocks.length=430 := by decide +kernel
theorem full_certificate_coverage : checkDegreeChain 5 1000000 blocks=true := by decide +kernel

#print axioms record_count
#print axioms full_certificate_coverage

end QuadraticTangZhang.CertificateData
