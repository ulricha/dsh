import Distribution.Simple
import Distribution.Simple.Program
import Distribution.Simple.Setup
import Distribution.Simple.LocalBuildInfo
import Distribution.Verbosity
import Distribution.PackageDescription
import Distribution.Text
import Distribution.System


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
  _ <- requireProgram verbose (simpleProgram "sh")   db
  _ <- requireProgram verbose (simpleProgram "rm")   db
  _ <- requireProgram verbose (simpleProgram "tar")  db
  _ <- requireProgram verbose (simpleProgram "cd")   db
  _ <- requireProgram verbose (simpleProgram "pwd")  db  
  _ <- requireProgram verbose (simpleProgram "make") db
  _ <- requireProgram verbose (simpleProgram "ar")   db
  _ <- requireProgram verbose (simpleProgram "ld")   db

  (preConf  simpleUserHooks) args flags
  
dshPreBuild :: Args -> BuildFlags -> IO HookedBuildInfo
dshPreBuild args flags = do
  db <- configureAllKnownPrograms silent defaultProgramConfiguration
  (sh,_) <- requireProgram verbose (simpleProgram "sh") db

  let dshArch = display buildArch

  let script = [ "rm -r -f pathfinder"
               , "tar xzf pathfinder.tar.gz"
               , "cd pathfinder"
               , "export CFLAGS='-arch " ++ dshArch ++ "'"
               , "sh configure --prefix=`pwd` --enable-static --disable-shared"
               , "make"
               , "make install"
               , "cd lib"
               , "ar x libpf_ferry.a"
               , "ld -r *.o -o C_Pathfinder.o"
               ]
  
  writeFile "pathfinder_pre_build.sh" (unlines script)
  runProgramInvocation verbose (programInvocation sh ["pathfinder_pre_build.sh"])


  (preBuild  simpleUserHooks) args flags

dshPostBuild :: Args -> BuildFlags -> PackageDescription -> LocalBuildInfo -> IO ()
dshPostBuild args flsgs desc info = do
  (postBuild simpleUserHooks) args flsgs desc info

  let dshBuildDir = buildDir info
  let dshVersion = display (pkgVersion (package desc))

  db <- configureAllKnownPrograms silent defaultProgramConfiguration
  (sh,_) <- requireProgram verbose (simpleProgram "sh") db

  let script = [  "ar -r -s "
                  ++ dshBuildDir ++ "/libHSDSH-Pathfinder-" ++ dshVersion ++ ".a "
                  ++ "pathfinder/lib/C_Pathfinder.o"
               ,  "ld -x -r -o "
                  ++ dshBuildDir ++ "/HSDSH-Pathfinder-" ++ dshVersion ++ ".o "
                  ++ dshBuildDir ++ "/HSDSH-Pathfinder-" ++ dshVersion ++ ".o "
                  ++ "pathfinder/lib/C_Pathfinder.o"
               ]
  
  writeFile "pathfinder_post_build.sh" (unlines script)
  runProgramInvocation verbose (programInvocation sh ["pathfinder_post_build.sh"])