package org.alfresco.maven.plugin;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.alfresco.repo.module.tool.ModuleManagementTool;
import org.apache.maven.RepositoryUtils;
import org.apache.maven.artifact.ArtifactUtils;
import org.apache.maven.execution.MavenSession;
import org.apache.maven.model.Dependency;
import org.apache.maven.model.DependencyManagement;
import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugin.MojoFailureException;
import org.apache.maven.project.MavenProject;
import org.codehaus.plexus.util.StringUtils;
import org.sonatype.aether.RepositorySystem;
import org.sonatype.aether.RepositorySystemSession;
import org.sonatype.aether.artifact.Artifact;
import org.sonatype.aether.artifact.ArtifactTypeRegistry;
import org.sonatype.aether.collection.CollectRequest;
import org.sonatype.aether.collection.DependencyCollectionContext;
import org.sonatype.aether.collection.DependencyCollectionException;
import org.sonatype.aether.collection.DependencySelector;
import org.sonatype.aether.collection.DependencyTraverser;
import org.sonatype.aether.graph.DependencyNode;
import org.sonatype.aether.graph.DependencyVisitor;
import org.sonatype.aether.util.FilterRepositorySystemSession;
import org.sonatype.aether.util.graph.selector.AndDependencySelector;
import org.sonatype.aether.util.graph.selector.ScopeDependencySelector;

/**
 * Performs a AMP to WAR overlay invoking the Alfresco Repository ModuleManagementTool. It therefore wraps and emulates the same WAR overlay
 * performed by Alfresco MMT.
 * <p/>
 * This goal will install the AMP file(s) found in ${ampLocation} onto the WAR (or exploded WAR) found in ${warLocation}
 *
 * @version $Id:$
 * @requiresDependencyResolution
 * @since 1.0
 * @goal install
 * @description Installs one or more AMPs onto an Alfresco / Share WAR (or exploded WAR folder)
 */
public class InstallMojo extends AbstractMojo
{

    private static final String WEBAPP_MANIFEST_PATH = "META-INF" + File.separator + "MANIFEST.MF";
    private static final String WEBAPP_DESCRIPTOR_PATH = "WEB-INF" + File.separator + "web.xml";

    /**
     * @parameter property="maven.alfresco.installFromDependencies" default-value="false"
     */
    private boolean installFromDependencies;

    /**
     * The location of the AMP file(s) to be installed. If this location is a folder all AMPs contained in the folder are installed, if it's
     * a file it get direclty installed on the ${warLocation}
     *
     * @parameter property="maven.alfresco.ampLocation" default-value="${project.build.directory}/${project.build.finalName}.amp"
     */
    private File ampLocation;

    /**
     * The WAR file or exploded dir to install the AMPs in. If specified Defaults to
     * <code>"${project.build.directory}/${project.build.finalName}-war</code>
     *
     * @parameter property="maven.alfresco.warLocation" default-value="${project.build.directory}/${project.build.finalName}.war"
     */
    private File warLocation;

    /**
     * Whether Alfresco MMT should be executed in verbose mode
     *
     * @parameter property="maven.alfresco.verbose" default-value="false"
     */
    private boolean verbose;

    /**
     * Whether Alfresco MMT should be force installation of AMPs
     *
     * @parameter property="maven.alfresco.force" default-value="true"
     */
    private boolean force;

    /**
     * Whether Alfresco MMT should produce backups while installing. Defaults to false to speed up development, set to true for Production
     * AMP installations
     *
     * @parameter property="maven.alfresco.backup" default-value="false"
     */
    private boolean backup;

    /**
     * Whether or not to skip the check for a manifest file in the warLocation
     *
     * @parameter property="maven.alfresco.skipWarManifestCheck" default-value="false"
     */
    private boolean skipWarManifestCheck;

    /**
     * (Read Only) The Maven project.
     *
     * @parameter default-value="${project}"
     * @required
     * @readonly
     */
    protected MavenProject project;

    /**
     * (Read Only) The Maven session
     *
     * @parameter default-value="${session}"
     * @readonly
     * @required
     */
    protected MavenSession session;

    /**
     * The entry point to Aether, i.e. the component doing all the work.
     *
     * @component
     */
    private RepositorySystem repoSystem;

    public InstallMojo()
    {
    }

    @Override
    public void execute() throws MojoExecutionException, MojoFailureException
    {
        // Checks appropriate input params are in place
        this.checkParams();
        final ModuleManagementTool mmt = new ModuleManagementTool();
        mmt.setVerbose(this.verbose);
        /**
         * Invoke the ModuleManagementTool to install AMP modules on the WAR file; if ampLocation is a folder all contained AMPs are
         * installed otherwise a single AMP install is attempted with the ampLocation
         */
        if (!this.installFromDependencies)
        {
            if (this.ampLocation.isDirectory())
            {
                try
                {
                    mmt.installModules(this.ampLocation.getAbsolutePath(), this.warLocation.getAbsolutePath(), false, // preview
                            this.force, // force install
                            this.backup); // backup
                }
                catch (final IOException e)
                {
                    throw new MojoExecutionException("ampLocation " + this.ampLocation.getAbsolutePath()
                            + " did not contain AMP files - AMP installation cannot proceed");
                } // backup
            }
            else if (this.ampLocation.isFile())
            {
                mmt.installModule(this.ampLocation.getAbsolutePath(), this.warLocation.getAbsolutePath(), false, // preview
                        this.force, // force install
                        this.backup); // backup
            }
            else
            {
                throw new MojoFailureException("ampLocation " + this.ampLocation.getAbsolutePath()
                        + " was neither an AMP file or a folder containing AMP files - AMP installation cannot proceed");
            }
        }
        else
        {
            final DependencyNode node = this.collectAMPDependencies();

            // this needs to be ordered
            // for reasons unknown, the dependency graph will not contain a dependency of a module if that module has already been listed as
            // a top level module
            // this can break our MOJO if we don't process artifacts in the same order for installing
            final Set<String> rootAMPArtifactKeys = new LinkedHashSet<String>();
            final Map<String, Collection<String>> artifactKeyToArtifactDependencies = new HashMap<String, Collection<String>>();

            this.buildArtifactDependencyRelations(node, rootAMPArtifactKeys, artifactKeyToArtifactDependencies);

            this.traverseDependenciesAndInstall(rootAMPArtifactKeys, artifactKeyToArtifactDependencies, mmt);
        }
    }

    private void traverseDependenciesAndInstall(final Set<String> rootAMPArtifactKeys,
            final Map<String, Collection<String>> artifactKeyToArtifactDependencies, final ModuleManagementTool mmt)
    {
        final Map<String, File> artifactKeyToAMPFile = new HashMap<String, File>();
        final Set<org.apache.maven.artifact.Artifact> artifacts = this.project.getDependencyArtifacts();
        for (final org.apache.maven.artifact.Artifact artifact : artifacts)
        {
            if ("amp".equals(artifact.getType()))
            {
                final File artifactFile = artifact.getFile();
                artifactKeyToAMPFile.put(ArtifactUtils.key(artifact), artifactFile);
            }
        }

        final Iterator<String> rootAMPIterator = rootAMPArtifactKeys.iterator();
        final Collection<String> installedModules = new HashSet<String>();
        while (rootAMPIterator.hasNext())
        {
            final String rootAMPKey = rootAMPIterator.next();

            final Stack<String> dependencyStack = new Stack<String>();
            dependencyStack.push(rootAMPKey);

            while (!dependencyStack.isEmpty())
            {
                // check remaining dependencies for current top-element
                final String currentModule = dependencyStack.peek();
                final Collection<String> dependencies = artifactKeyToArtifactDependencies.get(currentModule);

                if (dependencies == null || dependencies.isEmpty())
                {
                    // no dependencies - we may install the current stack top-element
                    this.getLog().debug("(Transitive) AMP dependency " + currentModule + " has no more unsatisfied dependencies");

                    if (!installedModules.contains(currentModule))
                    {
                        if (rootAMPArtifactKeys.contains(currentModule))
                        {
                            this.getLog().debug("Installing (transitive) AMP dependency " + currentModule);

                            final File artifactFile = artifactKeyToAMPFile.get(currentModule);
                            mmt.installModule(artifactFile.getAbsolutePath(), this.warLocation.getAbsolutePath(), false, // preview
                                    this.force, this.backup);
                        }
                        else
                        {
                            this.getLog().debug(
                                    "(Transitive) AMP dependency " + currentModule
                                            + " will not be installed since it has not been declared as a direct dependency");
                        }
                        installedModules.add(currentModule);
                    }
                    else
                    {
                        this.getLog().debug("(Transitive) AMP dependency " + currentModule + " has already been handled");
                    }

                    // completed this (transitive) dependency of root AMP
                    dependencyStack.pop();
                }
                else
                {
                    final String firstUnresolvedDependency = dependencies.iterator().next();
                    dependencies.remove(firstUnresolvedDependency);

                    if (!installedModules.contains(firstUnresolvedDependency))
                    {
                        this.getLog().debug(
                                "(Transitive) AMP dependency " + currentModule + " requires handling of its dependency "
                                        + firstUnresolvedDependency + " before it may be installed");
                        dependencyStack.push(firstUnresolvedDependency);
                    }
                }
            }
        }
    }

    private void buildArtifactDependencyRelations(final DependencyNode node, final Set<String> rootAMPArtifactKeys,
            final Map<String, Collection<String>> artifactKeyToArtifactDependencies)
    {
        final Stack<String> artifactStack = new Stack<String>();
        node.accept(new DependencyVisitor()
        {

            @Override
            public boolean visitEnter(final DependencyNode node)
            {
                final boolean isAmpDependency;
                final org.sonatype.aether.graph.Dependency dependency = node.getDependency();
                if (dependency != null)
                {
                    final Artifact artifact = dependency.getArtifact();
                    final String artifactKey = ArtifactUtils.key(artifact.getGroupId(), artifact.getArtifactId(), artifact.getVersion());
                    isAmpDependency = "amp".equals(artifact.getExtension());

                    final String dependingArtifactKey = artifactStack.isEmpty() ? null : artifactStack.peek();
                    if (dependingArtifactKey == null && isAmpDependency)
                    {
                        // top-level dependency
                        rootAMPArtifactKeys.add(artifactKey);
                    }
                    else if (dependingArtifactKey != null)
                    {
                        // transitive dependency
                        Collection<String> dependencies = artifactKeyToArtifactDependencies.get(dependingArtifactKey);
                        if (dependencies == null)
                        {
                            dependencies = new HashSet<String>();
                            artifactKeyToArtifactDependencies.put(dependingArtifactKey, dependencies);
                        }
                        dependencies.add(artifactKey);
                    }

                    artifactStack.push(artifactKey);
                }
                else
                {
                    isAmpDependency = true;
                }
                return isAmpDependency;
            }

            @Override
            public boolean visitLeave(final DependencyNode node)
            {
                if (node.getDependency() != null)
                {
                    artifactStack.pop();
                }
                return true;
            }
        });
    }

    private DependencyNode collectAMPDependencies() throws MojoFailureException
    {
        final ArtifactTypeRegistry stereotypes = this.session.getRepositorySession().getArtifactTypeRegistry();

        final CollectRequest collect = new CollectRequest();
        collect.setRequestContext("alfresco-maven-plugin:install");
        collect.setRepositories(this.project.getRemoteProjectRepositories());

        for (final Dependency dependency : this.project.getDependencies())
        {
            if (StringUtils.isEmpty(dependency.getGroupId()) || StringUtils.isEmpty(dependency.getArtifactId())
                    || StringUtils.isEmpty(dependency.getVersion()))
            {
                // guard against case where best-effort resolution for invalid models is requested
                continue;
            }

            if (!"amp".equals(dependency.getType()) || !"runtime".equals(dependency.getScope()))
            {
                // only interested in runtime-scope AMPs
                // Note: runtime-scope chosen because it does not interfere with WAR packaging, i.e. unwanted overlay of JARs from AMPs
                // in WEB-INF/lib
                continue;
            }

            collect.addDependency(RepositoryUtils.toDependency(dependency, stereotypes));
        }

        final DependencyManagement dependencyManagement = this.project.getDependencyManagement();
        if (dependencyManagement != null)
        {
            for (final Dependency dependency : dependencyManagement.getDependencies())
            {
                collect.addManagedDependency(RepositoryUtils.toDependency(dependency, stereotypes));
            }
        }

        DependencyNode node;
        try
        {
            node = this.repoSystem.collectDependencies(new AMPLookupSession(this.session.getRepositorySession()), collect).getRoot();
        }
        catch (final DependencyCollectionException ex)
        {
            throw new MojoFailureException("Failed to collect dependencies", ex);
        }
        return node;
    }

    private void checkParams() throws MojoExecutionException
    {
        if (!this.installFromDependencies)
        {
            if (this.ampLocation == null || !this.ampLocation.exists())
            {
                throw new MojoExecutionException("No AMP file(s) found in " + this.ampLocation.getAbsolutePath()
                        + " - AMP installation cannot proceed");
            }
        }
        if (this.warLocation == null || !this.warLocation.exists())
        {
            throw new MojoExecutionException("No WAR file found in " + this.warLocation.getAbsolutePath()
                    + " - AMP installation cannot proceed");
        }

        final File descriptor = new File(this.warLocation.getPath() + File.separator + WEBAPP_DESCRIPTOR_PATH);
        if (this.warLocation.isDirectory() && !descriptor.exists())
            throw new MojoExecutionException("No webapp found in " + descriptor.getAbsolutePath()
                    + ". AMP installation cannot proceed. Are you binding amp:install to the right phase?");

        final File manifest = new File(this.warLocation.getPath() + File.separator + WEBAPP_MANIFEST_PATH);
        if (!this.skipWarManifestCheck && this.warLocation.isDirectory() && !manifest.exists())
            throw new MojoExecutionException("No MANIFEST.MF found in " + manifest.getAbsolutePath()
                    + ". AMP installation cannot proceed. Are you binding amp:install to the right phase?");
    }

    private static class AMPLookupSession extends FilterRepositorySystemSession
    {

        protected AMPLookupSession(final RepositorySystemSession session)
        {
            super(session);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public DependencySelector getDependencySelector()
        {
            return new AndDependencySelector(new ScopeDependencySelector(Arrays.asList("compile", "runtime", "provided"), null),
                    new DependencySelector()
                    {

                        @Override
                        public boolean selectDependency(final org.sonatype.aether.graph.Dependency dependency)
                        {
                            // have to select JARs as well, since modules may depend only on other modules JAR instead of AMP
                            // (common approach in community)
                            final boolean jarOrAmp = "amp".equals(dependency.getArtifact().getExtension())
                                    || "jar".equals(dependency.getArtifact().getExtension());
                            return jarOrAmp;
                        }

                        @Override
                        public DependencySelector deriveChildSelector(final DependencyCollectionContext context)
                        {
                            return this;
                        }
                    });
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public DependencyTraverser getDependencyTraverser()
        {
            return new DependencyTraverser()
            {

                @Override
                public boolean traverseDependency(final org.sonatype.aether.graph.Dependency dependency)
                {
                    // traverse to dependencies of AMPs only
                    final boolean isAmp = "amp".equals(dependency.getArtifact().getExtension());
                    return isAmp;
                }

                @Override
                public DependencyTraverser deriveChildTraverser(final DependencyCollectionContext context)
                {
                    return this;
                }
            };
        }

    }
}