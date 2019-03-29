package uk.gov.hmcts.ccd;

import com.hazelcast.config.Config;
import com.hazelcast.config.MapConfig;
import com.hazelcast.config.MaxSizeConfig;
import com.hazelcast.config.NetworkConfig;

import java.util.Optional;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

@Configuration
public class CachingConfiguration {

    @Autowired
    ApplicationParams applicationParams;


    @Bean
    public Config hazelCastConfig() {

        Config config = new Config();
        NetworkConfig networkConfig = config.setInstanceName("hazelcast-instance-ccd").getNetworkConfig();
        networkConfig.getJoin().getMulticastConfig().setEnabled(false);
        networkConfig.getJoin().getTcpIpConfig().setEnabled(false);
        configCaches(applicationParams.getDefinitionCacheMaxIdleSecs(), applicationParams.getLatestVersionTTLSecs(), config);
        return config;
    }

    private void configCaches(int definitionCacheMaxIdle, int latestVersionTTL, Config config) {
        config.addMapConfig(newMapConfig("caseTypeDefinitionsCache", definitionCacheMaxIdle));
        config.addMapConfig(newMapConfig("workBasketResultCache", definitionCacheMaxIdle));
        config.addMapConfig(newMapConfig("searchResultCache", definitionCacheMaxIdle));
        config.addMapConfig(newMapConfig("searchInputDefinitionCache", definitionCacheMaxIdle));
        config.addMapConfig(newMapConfig("workbasketInputDefinitionCache", definitionCacheMaxIdle));
        config.addMapConfig(newMapConfig("caseTabCollectionCache", definitionCacheMaxIdle));
        config.addMapConfig(newMapConfig("wizardPageCollectionCache", definitionCacheMaxIdle));
        config.addMapConfig(newMapConfig("userRolesCache", definitionCacheMaxIdle));
        config.addMapConfig(newMapConfig("caseTypeDefinitionLatestVersionCache", definitionCacheMaxIdle, Optional.of(latestVersionTTL)));
        
    }

    private MapConfig newMapConfig(final String name, Integer definitionCacheMaxIdle) {
        return newMapConfig(name, definitionCacheMaxIdle, Optional.empty());
    }

    private MapConfig newMapConfig(final String name, Integer definitionCacheMaxIdle, Optional<Integer> latestVersionTTL) {
        MapConfig mapConfig = new MapConfig().setName(name)
                .setMaxSizeConfig(new MaxSizeConfig(applicationParams.getDefinitionCacheMaxSize(), MaxSizeConfig.MaxSizePolicy.PER_NODE))
                .setEvictionPolicy(applicationParams.getDefinitionCacheEvictionPolicy())
                .setMaxIdleSeconds(definitionCacheMaxIdle);
        latestVersionTTL.ifPresent(value -> mapConfig.setTimeToLiveSeconds(value));
        return mapConfig;
    }

}
