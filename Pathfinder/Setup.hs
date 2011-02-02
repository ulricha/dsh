import Distribution.Simple
import Distribution.Simple.Program
import Distribution.Simple.Setup
import Distribution.Simple.LocalBuildInfo
import Distribution.Verbosity
import Distribution.PackageDescription
import Distribution.Text
import Distribution.System

import System.Directory (doesFileExist)


main :: IO ()
main = defaultMainWithHooks dshHooks


dshHooks :: UserHooks
dshHooks = simpleUserHooks {
    preConf   = dshPreConf
  , preBuild  = dshPreBuild
  , postBuild = dshPostBuild
  }
  

dshPreConf ::  Args -> ConfigFlags -> IO HookedBuildInfo
dshPreConf args flags = do
  db <- configureAllKnownPrograms silent defaultProgramConfiguration
  _ <- requireProgram verbose (simpleProgram "sh")    db
  _ <- requireProgram verbose (simpleProgram "rm")    db
  _ <- requireProgram verbose (simpleProgram "cp")    db  
  _ <- requireProgram verbose (simpleProgram "tar")   db
  _ <- requireProgram verbose (simpleProgram "pwd")   db  
  _ <- requireProgram verbose (simpleProgram "make")  db
  _ <- requireProgram verbose (simpleProgram "ar")    db
  _ <- requireProgram verbose (simpleProgram "ld")    db

  (preConf  simpleUserHooks) args flags
  

dshPreBuild :: Args -> BuildFlags -> IO HookedBuildInfo
dshPreBuild args flags = do
  db <- configureAllKnownPrograms silent defaultProgramConfiguration
  (sh,_) <- requireProgram verbose (simpleProgram "sh") db

  let cflags = case buildArch of
                  I386   -> "-m32"
                  X86_64 -> "-m64"
                  PPC	   -> "-m32"
                  PPC64	 -> "-m64"
                  Sparc	 -> "-m64"
                  Arm	   -> "-m32"
                  Mips	 -> "-m64"
                  SH	   -> "-m32"
                  IA64	 -> "-m64"
                  S390	 -> "-m32"
                  Alpha  -> "-m64"
                  Hppa	 -> "-m64"
                  Rs6000 -> "-m64"
                  M68k	 -> "-m32"
                  Vax    -> "-m32"
                  _      -> ""

  let script = [ "rm -r -f pathfinder"
               , "tar xzf pathfinder.tar.gz"
               , "cd pathfinder"
               , "export CFLAGS=' " ++ cflags ++ " -fPIC -fno-jump-tables'"
               , "sh configure --prefix=`pwd` --enable-static --disable-shared --with-pic"
               , "make"
               , "make install"
               , "cd lib"
               , "ar x libpf_ferry.a"
               , "ld -r *.o -o CC_Pathfinder.o"
               ]
  
  writeFile "pathfinder_pre_build.sh" (unlines script)
  runProgramInvocation verbose (programInvocation sh ["pathfinder_pre_build.sh"])

  (preBuild  simpleUserHooks) args flags


dshPostBuild :: Args -> BuildFlags -> PackageDescription -> LocalBuildInfo -> IO ()
dshPostBuild args flags desc info = do
  (postBuild simpleUserHooks) args flags desc info

  let dshBuildDir = buildDir info
  let dshVersion = display (pkgVersion (package desc))

  db <- configureAllKnownPrograms silent defaultProgramConfiguration
  (sh,_) <- requireProgram verbose (simpleProgram "sh") db

  pb <- doesFileExist (dshBuildDir ++ "/libHSPathfinder-" ++ dshVersion ++ "_p.a")

  let script = [  "ar -r -s "
                  ++ dshBuildDir ++ "/libHSPathfinder-" ++ dshVersion ++ ".a "
                  ++ " pathfinder/lib/CC_Pathfinder.o "
               ,  if pb
                     then "ar -r -s "
                          ++ dshBuildDir ++ "/libHSPathfinder-" ++ dshVersion ++ "_p.a "
                          ++ " pathfinder/lib/CC_Pathfinder.o "
                     else []
               ,  "cp "
                  ++ dshBuildDir ++ "/HSPathfinder-" ++ dshVersion ++ ".o "
                  ++ "pathfinder/lib/HS_Pathfinder.o"
               ,  "ld -x -r -o "
                  ++ dshBuildDir ++ "/HSPathfinder-" ++ dshVersion ++ ".o "
                  ++ " pathfinder/lib/HS_Pathfinder.o "
                  ++ " pathfinder/lib/CC_Pathfinder.o "
               ]
  
  writeFile "pathfinder_post_build.sh" (unlines script)
  runProgramInvocation verbose (programInvocation sh ["pathfinder_post_build.sh"])
