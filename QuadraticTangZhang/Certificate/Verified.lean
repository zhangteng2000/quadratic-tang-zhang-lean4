import QuadraticTangZhang.Certificate.Assembly
import QuadraticTangZhang.Certificate.Checked00
import QuadraticTangZhang.Certificate.Checked01
import QuadraticTangZhang.Certificate.Checked02
import QuadraticTangZhang.Certificate.Checked03
import QuadraticTangZhang.Certificate.Checked04
import QuadraticTangZhang.Certificate.Checked05
import QuadraticTangZhang.Certificate.Checked06
import QuadraticTangZhang.Certificate.Checked07
import QuadraticTangZhang.Certificate.Checked08
import QuadraticTangZhang.Certificate.Checked09
import QuadraticTangZhang.Certificate.Checked10
import QuadraticTangZhang.Certificate.Checked11
import QuadraticTangZhang.Certificate.Checked12
import QuadraticTangZhang.Certificate.Checked13
import QuadraticTangZhang.Certificate.Checked14
import QuadraticTangZhang.Certificate.Checked15
import QuadraticTangZhang.Certificate.Checked16
import QuadraticTangZhang.Certificate.Checked17
import QuadraticTangZhang.Certificate.Checked18
import QuadraticTangZhang.Certificate.Checked19
import QuadraticTangZhang.Certificate.Checked20
import QuadraticTangZhang.Certificate.Checked21
import QuadraticTangZhang.Certificate.Checked22
import QuadraticTangZhang.Certificate.Checked23
import QuadraticTangZhang.Certificate.Checked24
import QuadraticTangZhang.Certificate.Checked25
import QuadraticTangZhang.Certificate.Checked26
import QuadraticTangZhang.Certificate.Checked27
import QuadraticTangZhang.Certificate.Checked28
import QuadraticTangZhang.Certificate.Checked29
import QuadraticTangZhang.Certificate.Checked30
import QuadraticTangZhang.Certificate.Checked31
import QuadraticTangZhang.Certificate.Checked32
import QuadraticTangZhang.Certificate.Checked33
import QuadraticTangZhang.Certificate.Checked34
import QuadraticTangZhang.Certificate.Checked35
import QuadraticTangZhang.Certificate.Checked36
import QuadraticTangZhang.Certificate.Checked37
import QuadraticTangZhang.Certificate.Checked38
import QuadraticTangZhang.Certificate.Checked39
import QuadraticTangZhang.Certificate.Checked40
import QuadraticTangZhang.Certificate.Checked41
import QuadraticTangZhang.Certificate.Checked42

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace QuadraticTangZhang.CertificateData

/-- J. All 430 blocks, assembled from the kernel proofs of all 6593 records. -/
theorem full_certificate_checked : allBlocksAccepted=true := by
  simp only [allBlocksAccepted, blocks, List.all_cons, List.all_nil,
    block_000_checked, block_001_checked, block_002_checked, block_003_checked, block_004_checked, block_005_checked, block_006_checked, block_007_checked, block_008_checked, block_009_checked,
    block_010_checked, block_011_checked, block_012_checked, block_013_checked, block_014_checked, block_015_checked, block_016_checked, block_017_checked, block_018_checked, block_019_checked,
    block_020_checked, block_021_checked, block_022_checked, block_023_checked, block_024_checked, block_025_checked, block_026_checked, block_027_checked, block_028_checked, block_029_checked,
    block_030_checked, block_031_checked, block_032_checked, block_033_checked, block_034_checked, block_035_checked, block_036_checked, block_037_checked, block_038_checked, block_039_checked,
    block_040_checked, block_041_checked, block_042_checked, block_043_checked, block_044_checked, block_045_checked, block_046_checked, block_047_checked, block_048_checked, block_049_checked,
    block_050_checked, block_051_checked, block_052_checked, block_053_checked, block_054_checked, block_055_checked, block_056_checked, block_057_checked, block_058_checked, block_059_checked,
    block_060_checked, block_061_checked, block_062_checked, block_063_checked, block_064_checked, block_065_checked, block_066_checked, block_067_checked, block_068_checked, block_069_checked,
    block_070_checked, block_071_checked, block_072_checked, block_073_checked, block_074_checked, block_075_checked, block_076_checked, block_077_checked, block_078_checked, block_079_checked,
    block_080_checked, block_081_checked, block_082_checked, block_083_checked, block_084_checked, block_085_checked, block_086_checked, block_087_checked, block_088_checked, block_089_checked,
    block_090_checked, block_091_checked, block_092_checked, block_093_checked, block_094_checked, block_095_checked, block_096_checked, block_097_checked, block_098_checked, block_099_checked,
    block_100_checked, block_101_checked, block_102_checked, block_103_checked, block_104_checked, block_105_checked, block_106_checked, block_107_checked, block_108_checked, block_109_checked,
    block_110_checked, block_111_checked, block_112_checked, block_113_checked, block_114_checked, block_115_checked, block_116_checked, block_117_checked, block_118_checked, block_119_checked,
    block_120_checked, block_121_checked, block_122_checked, block_123_checked, block_124_checked, block_125_checked, block_126_checked, block_127_checked, block_128_checked, block_129_checked,
    block_130_checked, block_131_checked, block_132_checked, block_133_checked, block_134_checked, block_135_checked, block_136_checked, block_137_checked, block_138_checked, block_139_checked,
    block_140_checked, block_141_checked, block_142_checked, block_143_checked, block_144_checked, block_145_checked, block_146_checked, block_147_checked, block_148_checked, block_149_checked,
    block_150_checked, block_151_checked, block_152_checked, block_153_checked, block_154_checked, block_155_checked, block_156_checked, block_157_checked, block_158_checked, block_159_checked,
    block_160_checked, block_161_checked, block_162_checked, block_163_checked, block_164_checked, block_165_checked, block_166_checked, block_167_checked, block_168_checked, block_169_checked,
    block_170_checked, block_171_checked, block_172_checked, block_173_checked, block_174_checked, block_175_checked, block_176_checked, block_177_checked, block_178_checked, block_179_checked,
    block_180_checked, block_181_checked, block_182_checked, block_183_checked, block_184_checked, block_185_checked, block_186_checked, block_187_checked, block_188_checked, block_189_checked,
    block_190_checked, block_191_checked, block_192_checked, block_193_checked, block_194_checked, block_195_checked, block_196_checked, block_197_checked, block_198_checked, block_199_checked,
    block_200_checked, block_201_checked, block_202_checked, block_203_checked, block_204_checked, block_205_checked, block_206_checked, block_207_checked, block_208_checked, block_209_checked,
    block_210_checked, block_211_checked, block_212_checked, block_213_checked, block_214_checked, block_215_checked, block_216_checked, block_217_checked, block_218_checked, block_219_checked,
    block_220_checked, block_221_checked, block_222_checked, block_223_checked, block_224_checked, block_225_checked, block_226_checked, block_227_checked, block_228_checked, block_229_checked,
    block_230_checked, block_231_checked, block_232_checked, block_233_checked, block_234_checked, block_235_checked, block_236_checked, block_237_checked, block_238_checked, block_239_checked,
    block_240_checked, block_241_checked, block_242_checked, block_243_checked, block_244_checked, block_245_checked, block_246_checked, block_247_checked, block_248_checked, block_249_checked,
    block_250_checked, block_251_checked, block_252_checked, block_253_checked, block_254_checked, block_255_checked, block_256_checked, block_257_checked, block_258_checked, block_259_checked,
    block_260_checked, block_261_checked, block_262_checked, block_263_checked, block_264_checked, block_265_checked, block_266_checked, block_267_checked, block_268_checked, block_269_checked,
    block_270_checked, block_271_checked, block_272_checked, block_273_checked, block_274_checked, block_275_checked, block_276_checked, block_277_checked, block_278_checked, block_279_checked,
    block_280_checked, block_281_checked, block_282_checked, block_283_checked, block_284_checked, block_285_checked, block_286_checked, block_287_checked, block_288_checked, block_289_checked,
    block_290_checked, block_291_checked, block_292_checked, block_293_checked, block_294_checked, block_295_checked, block_296_checked, block_297_checked, block_298_checked, block_299_checked,
    block_300_checked, block_301_checked, block_302_checked, block_303_checked, block_304_checked, block_305_checked, block_306_checked, block_307_checked, block_308_checked, block_309_checked,
    block_310_checked, block_311_checked, block_312_checked, block_313_checked, block_314_checked, block_315_checked, block_316_checked, block_317_checked, block_318_checked, block_319_checked,
    block_320_checked, block_321_checked, block_322_checked, block_323_checked, block_324_checked, block_325_checked, block_326_checked, block_327_checked, block_328_checked, block_329_checked,
    block_330_checked, block_331_checked, block_332_checked, block_333_checked, block_334_checked, block_335_checked, block_336_checked, block_337_checked, block_338_checked, block_339_checked,
    block_340_checked, block_341_checked, block_342_checked, block_343_checked, block_344_checked, block_345_checked, block_346_checked, block_347_checked, block_348_checked, block_349_checked,
    block_350_checked, block_351_checked, block_352_checked, block_353_checked, block_354_checked, block_355_checked, block_356_checked, block_357_checked, block_358_checked, block_359_checked,
    block_360_checked, block_361_checked, block_362_checked, block_363_checked, block_364_checked, block_365_checked, block_366_checked, block_367_checked, block_368_checked, block_369_checked,
    block_370_checked, block_371_checked, block_372_checked, block_373_checked, block_374_checked, block_375_checked, block_376_checked, block_377_checked, block_378_checked, block_379_checked,
    block_380_checked, block_381_checked, block_382_checked, block_383_checked, block_384_checked, block_385_checked, block_386_checked, block_387_checked, block_388_checked, block_389_checked,
    block_390_checked, block_391_checked, block_392_checked, block_393_checked, block_394_checked, block_395_checked, block_396_checked, block_397_checked, block_398_checked, block_399_checked,
    block_400_checked, block_401_checked, block_402_checked, block_403_checked, block_404_checked, block_405_checked, block_406_checked, block_407_checked, block_408_checked, block_409_checked,
    block_410_checked, block_411_checked, block_412_checked, block_413_checked, block_414_checked, block_415_checked, block_416_checked, block_417_checked, block_418_checked, block_419_checked,
    block_420_checked, block_421_checked, block_422_checked, block_423_checked, block_424_checked, block_425_checked, block_426_checked, block_427_checked, block_428_checked, block_429_checked, Bool.and_self]

theorem full_certificate_evaluates_successfully : records.all verifyStandardRecord=true :=
  accepted_records_of_blocks full_certificate_checked

#print axioms full_certificate_checked
#print axioms full_certificate_evaluates_successfully

end QuadraticTangZhang.CertificateData
